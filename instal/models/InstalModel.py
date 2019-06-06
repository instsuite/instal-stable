import os
from abc import ABCMeta
from collections import defaultdict
from typing import List, IO

from instal.clingo import Symbol

from instal.compiler.InstalCompilerNew import InstalCompilerNew
from instal.domainparser.DomainParser import DomainParser
from instal.factparser.FactParser import FactParser
from instal.instalexceptions import InstalFileNotFound
from instal.instalutility import temporary_text_file
from instal.parser.InstalParserNew import InstalParserNew
from instal.state.InstalStateTrace import InstalStateTrace
from instal import InstalFile
INSTAL_STANDARD_PRELUDE = """
% Surpress Clingo warnings
ifluent(0,0).
nifluent(0,0).
oblfluent(0,0).
initiated(0,0,0,0).
xinitiated(0,0,0,0,0).
terminated(0,0,0,0).
xterminated(0,0,0,0,0).
_typeNotDeclared :- 1 == 2.
bridge(1).

% TIME
start(0).
instant(0..T) :- final(T).
next(T,T+1) :- instant(T).
final(horizon).

% TODO: Remove the need for this in constraint generation
true.

% CREATION
% Event: _create_ (type: ex)
event(_create_) :- true.
evtype(_create_,X,ex) :- inst(X).
evinst(_create_,X) :- inst(X).
ifluent(pow(_create_),X) :- inst(X).
ifluent(perm(_create_),X) :- inst(X).
fluent(pow(_create_),X) :- inst(X).
fluent(perm(_create_),X) :- inst(X).
event(viol(_create_)) :- true.
evtype(viol(_create_),X,viol) :- inst(X).
evinst(viol(_create_),X) :- inst(X).
holdsat(live(X),X,_create_,I) :- start(I), inst(X).
holdsat(perm(_create_),X,_create_,I) :- start(I), inst(X).
holdsat(pow(_create_),X,_create_,I) :- start(I), inst(X).

% FLUENT RULES
fluentterminated(P, In, I) :- terminated(P, In, _, I), instant(I), inst(In).
fluentterminated(P, In, I) :- xterminated(InS, P, In, _, I), instant(I), inst(In), inst(InS).
fluentinitiated(P, In, E, I) :- initiated(P, In, E, I), instant(I), inst(In), event(E).
fluentinitiated(P, In, E, I) :- xinitiated(InSo, P, In, E, I), inst(InSo), inst(In), instant(I), event(E).
holdsat(P,In,E,J):- holdsat(P,In,E,I),not fluentterminated(P,In,I),
	next(I,J),ifluent(P, In),instant(I),instant(J), inst(In), event(E).
holdsat(P,In,E,J):- fluentinitiated(P,In,E,I),next(I,J),
	ifluent(P, In),instant(I),instant(J), inst(In), event(E).

holdsat(P,In,E,J):- holdsat(P,In,E,I),not fluentterminated(P,In,I),
	next(I,J),ifluent(P, In),instant(I),instant(J), bridge(In), event(E).
holdsat(P,In,E,J):- initiated(P,In,E,I),next(I,J),
	ifluent(P, In),instant(I),instant(J), bridge(In), event(E).

% EXTERNAL FLUENTS
#external holdsat(F,I) : ifluent(F,I), inst(I).
% need to make _create_ something the user can't write
holdsat(F,I,_create_,J) :- holdsat(F,I), start(J).

% EVENTS OCCUR
% note use of _ in holdsat in next two rules; ought not to matter
occurred(E,In,I):- evtype(E,In,ex),observed(E,In,I),instant(I), inst(In), holdsat(pow(E),In,_,I).
occurred(_unempoweredEvent(E), In, I) :- evtype(E,In,ex),observed(E,In,I),instant(I), inst(In), not holdsat(pow(E),In,_,I).
occurred(_unrecognisedEvent(E),In,I) :- not evtype(E,In,ex), observed(E,In,I),
	instant(I), inst(In).

occurred(null,In,I) :- not evtype(E,In,ex), observed(E,In,I),
	instant(I), inst(In). % TODO: What's the point of the null anyway?


% for observation sequences
#external extObserved(E,I) : event(E), evtype(E,_,ex), instant(I).

recEvent(I) :- extObserved(E, I), event(E), instant(I), not final(I).
extObserved(_unrecognisedEvent, I) :- not recEvent(I), _eventSet(I).

%EVENT SET
#external _eventSet(I) : instant(I).

% VIOLATIONS FOR NON-PERMITTED EVENTS
% note use of _ in holdsat twice here; ought not to matter
occurred(viol(E),In,I):-
	occurred(E,In,I),
	not holdsat(perm(E),In,_,I),
	holdsat(live(In),In,_,I),evinst(E,In),
	event(E),instant(I),event(viol(E)),inst(In).

%%  mode COMPOSITE is chosen:\n
1 {genObserved(E, J) : evtype(E, In, ex), inst(In)} 1:- instant(J), not final(J), not extObserved(_, J).
:- observed(E,J),observed(F,J),instant(J),evtype(E,InX,ex),
   evtype(F,InY,ex), E!=F,inst(InX;InY).
obs(I):- observed(_,I),instant(I).
:- not obs(I), not final(I), instant(I), inst(In).
observed(E, I) :- genObserved(E, I), not final(I).
observed(E, I) :- extObserved(E, I), not final(I).
observed(E,In,I) :- observed(E,I), inst(In), instant(I).

:- _typeNotDeclared. %defends against partially grounded institutions.

_preludeLoaded.

#show observed/2.
#show occurred/3.
#show holdsat/4.
#show initiated/4.
#show terminated/4.

% drop answer sets with _create_ events
:- observed(_create_,I).
"""


class InstalModel(metaclass=ABCMeta):
    """
        InstalModel
        Wrapper for different implementations of InstAL solving.
        See: InstalMultiShotModel and InstalSingleShotModel
    """

    def __init__(self, ial_files: List[InstalFile], bridge_files: List[InstalFile],
                 lp_files: List[InstalFile],
                 domain_files: List[InstalFile], fact_files: List[InstalFile]):
        self.prelude = temporary_text_file(
            INSTAL_STANDARD_PRELUDE, file_extension=".lp", delete=True)

        self.model_files = self.get_model_files(ial_files, bridge_files) + [temporary_text_file(l.read(),file_extension=".lp", delete=True) for l in lp_files]
        print(self.model_files)
        self.domain_facts = self.get_domains(domain_files)

        self.initial_facts = self.get_initial(fact_files)
        self.answersets = [] # type: List[InstalStateTrace]

    def check_file_exists(self, filename, descriptor="File"):
        if os.path.isfile(filename):
            return
        raise InstalFileNotFound("File not found: {} ({})".format(filename,descriptor))

    def get_model_files(self, ial_files, bridge_files):
        parser_wrapper = InstalParserNew()
        compiler_wrapper = InstalCompilerNew()

        instal_dictionary = parser_wrapper.get_instal_dictionary(
            ial_files, bridge_files)
        irs_dictionary = parser_wrapper.parse(instal_dictionary)
        asp_dictionary = compiler_wrapper.compile(irs_dictionary)
        # print(asp_dictionary["institution_asp"][0]["contents"])
        output_files = []
        for a in asp_dictionary["institution_asp"]:
            output_files.append(a["file"])

        for a in asp_dictionary["bridge_asp"]:
            output_files.append(a["file"])

        output_files.append(self.prelude)

        return output_files

    def get_domains(self, domain_files : List[InstalFile]) -> defaultdict(set):
        domain_parser = DomainParser()
        domain_facts = domain_parser.get_groundings(domain_files)
        return domain_facts

    def get_initial(self, fact_files : List[InstalFile]) -> List[Symbol]:
        fact_parser = FactParser()
        facts = fact_parser.get_facts(fact_files)
        return facts

    def check_and_output_json(self, json_file) -> None:
        if json_file:
            self.output_json(json_file)

    def output_json(self, json_file):
        if os.path.isdir(json_file):
            self.output_json_dir(json_file)
        else:
            self.output_json_file(json_file)

    def output_json_file(self, json_file):
        base_dir, base_filename = os.path.split(json_file)
        for trace in self.answersets:
            trace.to_json_file(trace.get_json_filename(base_dir=base_dir, filename=base_filename))

    def output_json_dir(self, json_file):
        for trace in self.answersets:
            trace.to_json_file(trace.get_json_filename(base_dir=json_file))

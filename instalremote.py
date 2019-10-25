#! /usr/bin/env python
import requests
from instal.instalargparse import getqueryargs, check_args
import os
from instal.instalutility import InstalFile
from typing import List, Optional
import simplejson as json
from instal.domainparser import DomainParser
import time

INSTAL_API = os.environ.get("INSTAL_REMOTE_URL","http://127.0.0.1:5000")
def instal_remote():
    args, unk = getqueryargs()
    instal_remote_with_args(args, unk)

def instal_remote_with_args(args, unk):
    args, unk = check_args(args,unk,query=True)
    ial_files = [open(f, "rt") for f in args.ial_files]
    bridge_files = [open(f,"rt") for f in args.bridge_files]
    lp_files = [open(f,"rt") for f in args.lp_files]
    domain_files = [open(f, "rt") for f in args.domain_files]
    fact_files = [open(f,"rt") for f in args.fact_files]
    query_file = open(args.query,"rt") if args.query else None
    json_file = args.json_file if args.json_file else None

    return instal_remote_files(ial_files=ial_files,bridge_files=bridge_files,
                              lp_files=lp_files,domain_files=domain_files,
                              fact_files=fact_files,query_file=query_file,
                                        json_file=json_file,
                                        verbose=args.verbose,answerset=args.answer_set,
                                        length=args.length,number=args.number)

def instal_remote_files(ial_files : List[InstalFile], bridge_files : List[InstalFile] = None, lp_files : List[InstalFile] = None,
        domain_files : List[InstalFile] = None, fact_files : List[InstalFile] = None, query_file : Optional[InstalFile] = None,
        json_file : Optional[str] = None, verbose : int = 0, answerset : int = 0, length : int = 0, number : int = 1):
    if not ial_files: ial_files = []
    if not bridge_files: bridge_files = []
    if not lp_files: lp_files = []
    if not domain_files: domain_files = []
    if not fact_files: fact_files = []
    old_types = DomainParser.DomainParser().get_groundings(domain_files)
    types = {}
    for k, v in old_types.items():
        types[k] = list(v)
    q = [l.replace("\n","")[9:][:-1] for l in query_file] if query_file else []

    response = requests.post(INSTAL_API + "/new/",
                             data=json.dumps(
                                 {"institutions": [i.read() for i in ial_files],
                                  "bridges": [b.read() for b in bridge_files],
                                  "types": types,
                                  "length": length,
                                  "facts": [f.read() for f in fact_files],
                                  "query": q,
                                  "number" : number}
                             ),
                             headers={'Content-Type': 'application/json'})

    assert(response.status_code==201)
    json_resp = response.json()
    model_id, grounding_id, query_id = json_resp.get("grounding", {}).get("model", {}).get("id"), json_resp.get(
        "grounding", {}).get("id"), json_resp.get("id")

    print("Successful send. Processing...")
    n = 30
    status = ""
    while n > 0:
        response = requests.get(INSTAL_API + "/model/{}/grounding/{}/query/{}/".format(
            model_id, grounding_id, query_id
        )
                                ,
                                headers={'Accept': 'application/json'})

        if (response.status_code == 200):
            status = response.json().get("status")
            if status == "error" or status == "complete":
                break
        n -= 1
        time.sleep(0.1)
    if status == "complete":
        json_resp = response.json()
        print("Complete")
        n_answersets = json_resp.get("n_answer_sets",1)
        print("Number of answersets: {}".format(n_answersets))
        answer_set_id = 0

        if verbose:
            if n_answersets == 1:
                answer_set_id = 1
            while not ((answer_set_id == "all") or (int(answer_set_id) >= 1 and int(answer_set_id) <= n_answersets)):
                answer_set_id = input("Please enter the number of the answer set you want to see the text output for (1-{}, all): ".format(n_answersets))
            if answer_set_id == "all":
                for answer_set_id in range(1,n_answersets+1):
                    print_text_for(model_id, grounding_id, query_id, answer_set_id)
            else:
                print_text_for(model_id,grounding_id,query_id,answer_set_id)

        if json_file:
            if n_answersets == 1:
                answer_set_id = 1
            while not ((answer_set_id == "all") or (int(answer_set_id) >= 1 and int(answer_set_id) <= n_answersets)):
                answer_set_id = input("Please enter the number of the answer set you want to save the json output for (1-{}, all): ".format(n_answersets))
            if answer_set_id == "all":
                for answer_set_id in range(1,n_answersets+1):
                    j = get_json_for(model_id,grounding_id,query_id,answer_set_id)
                    dump_json_to_file(j,"{}_{}".format(answer_set_id,json_file))
            else:
                j = get_json_for(model_id, grounding_id, query_id, answer_set_id)
                dump_json_to_file(j,json_file)
    elif status == "error":
        print("Error")
        json_resp = response.json()
        error, message = json_resp.get("errors")[0], json_resp.get("errors")[1]
        print(error)
        print(message)
        return
    else:
        print("Failed to complete in time.")
        return

def print_text_for(model_id,grounding_id,query_id,answer_set_id):
    response = requests.get(INSTAL_API + "/model/{}/grounding/{}/query/{}/output/{}/".format(
        model_id, grounding_id, query_id, answer_set_id),
                            headers={"Accept": "text/plain"})
    assert (response.status_code == 200)
    print(response.text)

def get_json_for(model_id,grounding_id,query_id,answer_set_id):
    response = requests.get(INSTAL_API + "/model/{}/grounding/{}/query/{}/output/{}/".format(
        model_id, grounding_id, query_id, answer_set_id),
                            headers={"Accept": "application/json"})
    assert (response.status_code == 200)
    return response.json()

def dump_json_to_file(json_data,filename):
    with open(filename,"wt") as f:
        print("Saving json in file {}...".format(filename))
        json.dump(json_data,f)

if __name__ == "__main__":
    instal_remote()


# InstAL: The Institutional Action Language.
The Institutional Action Language (InstAL) is a tool for specifying, modelling and verifying electronic institutions.

At the heart of InstAL is Answer Set Programming - institutional definitions are compiled into Answer Set Prolog (AnsProlog.) That AnsProlog program is then solved in different ways based on what operations the user wishes to perform with the institution.

# Installation Instructions
Installation instructions are available in INSTALLATION.md

# Running InstAL
There are three executable InstAL scripts in this directory:
- instalquery.py - for solving locally.
- instalremote.py - for solving on an instance of InstAL-REST. By default it points at http://127.0.0.1:5000/. Set the environment variable INSTAL_REMOTE_URL to use another service.
- instaltrace.py - for different ways of processing and representing InstAL's json output.

All three of these scripts have help functionality. Append "--help" to the script on the command line.

# Further information & Instructions
More InstAL information is available from http://instsuite.github.io/

# Tests
You can run the tests in the firstprinciples/ directory using the script ./ts. This by default will run the tests locally. Set the environment variable INSTAL_NOSE_API_URL to use an instance of InstAL-REST.

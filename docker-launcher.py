import os
import sys

# query, remote, trace
if len(sys.argv) > 1:
    os.system('python3 instal' + sys.argv[1].lower() + '.py ' + " ".join(sys.argv[2:]))
else:
    print("...print help statement here.... [invalid syntax: missing arguments]")
    exit(1)
    


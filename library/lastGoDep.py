import re
from datetime import datetime
import sys
import subprocess
import pyperclip

output = subprocess.check_output(['git', 'log', '-1'])
res = output.decode('utf-8')
print("\033[33m" + res + "\033[0m")

input_str = res #sys.argv[1]
# """
# commit b86a7dce6a03def7a898740817b57da5a5b233f2 (origin/master, origin/HEAD, master)
# Merge: 5845377 5cce77d
# Author: Linard Arquint <linard.arquint@inf.ethz.ch>
# Date:   Thu Jul 13 17:04:55 2023 +0200
# """

commit_hash = re.search(r'commit (\w+)', input_str).group(1)
commit_res = commit_hash[:12]
# print(commit_res)

date_res = re.search(r'Date:\s+[a-zA-Z]+ ([a-zA-Z]+ [0-9]+) ([0-9]+):([0-9]+):([0-9]+) ([0-9]+) \+([0-9][0-9])', input_str)
# print(date_res.groups())

date_obj = datetime.strptime(date_res.group(1), "%b %d")
date_obj_res = date_obj.strftime("%m%d")

hour_int = int(date_res.group(2)) - int(date_res.group(6))
hour_str = "{:02d}".format(hour_int)

date_go = date_res.group(5) + date_obj_res + hour_str + date_res.group(3) + date_res.group(4)
# print(date_go)

version_str = f'v0.0.0-{date_go}-{commit_res}'
print("\033[1m" + version_str + "\033[0m")
# print(version_str == "v0.0.0-20230713150455-b86a7dce6a03")

# Copy the result to the clipboard
pyperclip.copy(version_str)


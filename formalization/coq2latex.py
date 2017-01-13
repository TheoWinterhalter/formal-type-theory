#!/usr/bin/python
import sys
import re
from string import Template

def rule2latex(name, premises, conclusion):
    return Template(
r"""\newcommand{\rl$name}{\referTo{$name}{rul:$name}}
\newcommand{\show$name}{%
    \infer[\rulename{$name}]
    {$premises}
    {$conclusion}
}""").substitute({"name" : name,
                  "premises" : r" \\ ".join(premises),
                  "conclusion" : conclusion})


### MAIN PROGRAM

# load the source file
with open(sys.argv[1], "r") as f:
    src = f.read()

for rule in re.findall(
        r'^\s*\|\s+'                   # the beginning of a rule
        r'(?P<rulename>\w+)\s*:\s*$'   # rule name
        r'\s*rule\s*'                 # header
        r'(?P<rulebody>.*?)'           # rule body
        r'endrule',                    # footer
        src,
        re.DOTALL + re.MULTILINE):
    rulename = rule[0]
    rulebody = rule[1]
    m = re.match(
        r'^(\s*parameters:.*?,)?'                 # optional parameters
        r'(?P<premises>.*?)'                      # premises
        r'conclusion:\s*(?P<conclusion>.*)\s*$',  # the rest is the rule
        rulebody,
        re.DOTALL)
    if not m:
        print ("Failed to parse rule {0} whose body is:\n{1}".format(rulename, rulebody))
        assert False
    premises = re.split(r'\s*premise:\s*', m.group('premises'))
    if len(premises) > 1 and not premises[0]: premises = premises[1:]
    conclusion = m.group('conclusion')
    print ("\n===={0}====\n".format(rulename))
    print (rule2latex(rulename, premises, conclusion))

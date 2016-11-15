#!/bin/bash
import re
import subprocess

rules = set([])

with open("rules.tex", "r") as r:
    for line in r:
        m = re.search(r'\\rl(\w+)', line)
        if m:
            rule = m.group(1)
            if rule in rules:
                print ('!!! DUPLICATE RULE {0} !!!'.format(rule))
            rules.add(rule)

print ("{0} rules loaded.".format(len(rules)))
                
with open("sanity.tex", "r") as f:
    with open("sanity.dot", "w") as g:
        g.write("digraph SanityGraph {")
        src = None
        trg = None
        for line in f:
            m = re.search(r'\\show(\w+)', line)
            if m:
                if src is not None:
                    g.write('{0} -> {{ {1} }}; \n'.format(src, " ".join(trg)))
                src = m.group(1)
                if src not in rules:
                    print ('!!! UNKNOWN SOURCE RULE {0} !!!'.format(src))
                trg = set([])
            else:
                m = re.search(r'^% ENDS WITH (\w+)', line);
                if m and src:
                    t = m.group(1)
                    trg.add(t)
                    if t not in rules and t not in ['IH', 'Premise', 'Inversion']:
                        print ('!!! UNKNOWN TARGET RULE {0} !!!'.format(t))

        g.write("}")

returnCode = subprocess.call(["acyclic", "-n", "sanity.dot"])
if returnCode != 0:
    print ("!!! THE GRAPH IS NOT ACYCLIC !!!")

subprocess.call(["dot", "-Tpdf", "-O", "sanity.dot"])

print ("Wrote sanity.dot.pdf")

# Then you do:
# python graph.py > foo.dot
# dot -Tpdf foo.dot > foo.pdf

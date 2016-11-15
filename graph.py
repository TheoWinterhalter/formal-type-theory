#!/bin/bash
import re
import subprocess

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
                trg = set([])
            else:
                m = re.search(r'^% ENDS WITH (\w+)', line);
                if m and src:
                    trg.add(m.group(1))
        g.write("}")

returnCode = subprocess.call(["acyclic", "-n", "sanity.dot"])
if returnCode != 0:
    print ("!!! THE GRAPH IS NOT ACYCLIC !!!")

subprocess.call(["dot", "-Tpdf", "-O", "sanity.dot"])


# Then you do:
# python graph.py > foo.dot
# dot -Tpdf foo.dot > foo.pdf

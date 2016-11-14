#!/bin/bash
import re

with open("sanity.tex", "r") as f:
    print ("digraph TypeTheory {")
    src = None
    trg = None
    for line in f:
        m = re.search(r'\\show(\w+)', line)
        if m: 
            if src is None:
                src = m.group(1)
                trg = set([])
            else:
                print ('{0} -> {{ {1} }}; \n'.format(src, " ".join(trg)))
                trg = set([])
        else:
            m = re.search(r'\\rl(\w+)', line);
            if m:
                if src:
                    trg.add(m.group(1))
    print("}")

# Then you do:
# python graph.py > foo.dot
# dot -Tpdf foo.dot > foo.pdf

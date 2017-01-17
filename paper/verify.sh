#!/bin/bash

# The script checks that rules.tex, sanity.tex and tt.tex have the same rules
# in the same order.

sanityRules=$(sed -n 's/^.*section\*{Rule {\\rl\([A-Za-z]+\)}.*$/\1/p' sanity.tex)
rulesRules=$(sed -n 's/^.*\\rl\([A-Za-z]+\)}.*$/\1/p' rules.tex)
ttRules=$(sed -n 's/^.*\\show\([A-Za-z]+\)}.*$/\1/p' tt.tex)
coqRules=$(sed -n 's/^.*| \([A-Za-z]+\) :.*$//p' ../formalization/ett.v)

echo "Checking sanity.tex against rules.tex:"
diff <(echo "$rulesRules") <(echo "$sanityRules")

echo "Checking tt.tex against rules.tex:"
diff <(echo "$rulesRules") <(echo "$ttRules")

echo "Checking reflections.v against rules.tex:"
diff <(echo "$rulesRules") <(echo "$coqRules")




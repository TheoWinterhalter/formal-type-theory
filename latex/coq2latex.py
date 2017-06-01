#!/usr/bin/env python
import sys
import re
import argparse
import subprocess
from string import Template

keywords = {
    'G' : 'Gamma',
    'D' : 'Delta',
    'E' : 'Theta',
    'ctxempty' : 'ctxempty',
    'sb' : 'sigma',
    'sbs' : 'sigma',
    'sbt' : 'tau',
    'sbr' : 'rho',
    'Bool' : 'Bool',
    'Unit' : 'Unit',
    'Empty' : 'Empty',
    'true' : 'true',
    'false' : 'false',
    'sbid' : 'sbid'
}

macros = {
    'isctx' : (1, 'isctx'),
    'istype' : (2, 'istype'),
    'isterm' : (3, 'isterm'),
    'issubst' : (3, 'issubst'),
    'eqtype' : (3, 'eqtype'),
    'eqterm' : (4, 'eqterm'),
    'eqctx' : (2, 'eqctx'),
    'eqsubst' : (4, 'eqsubst'),
    'ctxextend' : (2, 'ctxextend'),
    'lam' : (3, 'lam'),
    'Prod' : (2, 'Prod'),
    'Id' : (3, 'Id'),
    'refl' : (2, 'refl'),
    'j' : (6, 'J'),
    'Subst' : (2, 'subst'),
    'subst' : (2, 'subst'),
    'sbweak' : (1, 'sbweak'),
    'sbshift' : (2, 'sbshift'),
    'sbcomp' : (2, 'sbcomp'),
    'sbzero' : (2, 'sbzero'),
    'var' : (1, 'var'),
    'S' : (1, 'suc'),
    'cond' : (4, 'cond'),
    'SimProd' : (2, 'SimProd'),
    'U' : (1, 'Uni'),
    'El' : (1, 'El'),
    'pair' : (4, 'pair'),
    'proj1' : (3, 'proj1'),
    'proj2' : (3, 'proj2'),
    'uniProd' : (3, 'uniProd'),
    'uniId' : (4, 'uniId'),
    'uniEmpty' : (1, 'uniEmpty'),
    'uniUnit' : (1, 'uniUnit'),
    'uniBool' : (1, 'uniBool'),
    'uniSimProd' : (3, 'uniSimProd'),
    'uniUni' : (1, 'uniUni')
}

# We're actually going to parse stuff here, so we work with
# a stream of tokens.

class TokenStream():
    def __init__(self, s):
        self.tokens = [t for t in re.split(r'\s+|([()])', s.strip()) if t]

    def __str__(self):
        return " ".join(self.tokens)

    def peek(self):
        return (self.tokens[0] if len(self.tokens) > 0 else None)

    def pop(self):
        if len(self.tokens) > 0:
            t = self.tokens.pop(0)
            return t
        else:
            return None

def die(msg):
    raise SyntaxError(msg)

def embrace(s):
    return '{' + s + '}'

def bk(s):
    return '\\' + s

def subscribe(t, s):
    return "{0}_{{{1}}}".format(t, s) if s else t

class Ident():
    def __init__(self, keyword):
        m = re.match(r'^(.*?)(\d+)$', keyword)
        if m:
            self.keyword = m.group(1)
            self.subscript = m.group(2)
        else:
            self.keyword = keyword
            self.subscript = 0

    def __str__(self):
        if self.keyword in keywords:
            return embrace(subscribe(bk(keywords[self.keyword]), self.subscript))
        elif len(self.keyword) == 1:
            return subscribe(self.keyword, self.subscript)
        else:
            return subscribe(r'\mathtt{{{0}}}'.format(self.keyword), self.subscript)

    def makeApp(self, args):
        if len(args) == 0:
            return self
        else:
            return Application(self, args)

    def is_macro(self):
        return self.keyword in macros

class Application():
    def __init__(self, head, args):
        self.head = head
        self.args = args

    def is_macro(self):
        return False

    def makeApp(self, args):
        return Application(self.head, self.args + args)

    def __str__(self):
        if self.head.is_macro():
            (arity, m) = macros[self.head.keyword]
            if len(self.args) != arity:
                die("macro {0} expects {1} arguments but got {2}".format(m, arity,
                                                                        len(self.args)))
            else:
                return "{0}{1}".format(bk(m), "".join([embrace(str(a)) for a in self.args ]))
        else:
            return "{0}\, {1}".format(str(self.head), "\, ".join(map(str, self.args)))

def parseSimple(tok):
    if tok.peek() == '(':
        tok.pop()
        e = parseApply(tok)
        if tok.pop() != ')':
            die("parsing: expected )".format(c))
        return e
    elif tok.peek() is not None and bool(re.match(r'\w+', tok.peek())):
        t = tok.pop()
        ob =  Ident(t)
        return ob
    else:
        return None

def parseApply(tok):
    head = parseSimple(tok)
    args = []
    t = parseSimple(tok)
    while t is not None:
        args.append(t)
        t = parseSimple(tok)
    return head.makeApp(args)

def parseExpr(tok):
    e = parseApply(tok)
    if tok.pop() is not None:
        die ("premature end")
    return e

def ruleName(rulename):
    # We might possibly remove weird characters or some such
    return rulename

def rule2latex(name, preconds, premises, conclusion):
    preconds = [str(parseExpr(TokenStream(precond))) for precond in preconds]
    premises = [str(parseExpr(TokenStream(premise))) for premise in premises]
    conclusion = str(parseExpr(TokenStream(conclusion)))

    colorPreconds = [Template(r'{\color{precondColor} $precond}').substitute({'precond':precond})
                     for precond in preconds]

    # NB: below you should keep the space in front of $premises so that axioms looks right

    return Template(
r"""\newcommand{\rule$ruleName}{\ruleRef{$ruleName}{rule:$ruleName}}
\newcommand{\show$ruleName}{%
    \infer
    { $premises}
    {$conclusion}
}
\newcommand{\show${ruleName}Paranoid}{%
    \infer
    { $colorPreconds $separator $premises}
    {$conclusion}
}
""").substitute({"ruleName" : ruleName(name),
                 "colorPreconds" : " \\\\\n".join(colorPreconds),
                 "premises" : " \\\\\n".join(premises),
                 "separator" : (r'\\\\' if len(preconds) > 0 else ''),
                 "conclusion" : conclusion})

def section(macroFile, title, src):
    """Process one inductive definition."""

    # We parse the rules and create macro definitions from them

    macroFile.write ('\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n')
    macroFile.write ('% {0}\n'.format(title))

    rules = re.findall(
            r'^\s*\|\s+'                   # the beginning of a rule
            r'(?P<rulename>\w+)\s*:\s*$'   # rule name
            r'\s*rule\s*'                  # header
            r'(?P<rulebody>.*?)'           # rule body
            r'endrule',                    # footer
            src,
            re.DOTALL + re.MULTILINE)

    for rule in rules:
        rulename = rule[0]
        rulebody = rule[1]
        m = re.match(
            r'^(\s*parameters:.*?,)?'                 # optional parameters
            r'(?P<premises>.*?)'                      # premises
            r'conclusion:\s*(?P<conclusion>.*)\s*$',  # the rest is the rule
            rulebody,
            re.DOTALL)
        if not m:
            die ("Failed to parse rule {0} whose body is:\n{1}".format(rulename, rulebody))

        # Get premises and preconditions
        pres = re.split(r'\s*(premise|precond):\s*', m.group('premises'))
        if len(pres) > 0 and not pres[0]: pres.pop(0)
        premises = []
        preconds = []
        isPrecond = None
        for word in pres:
            if word == 'premise':
                isPrecond = False
            elif word == 'precond':
                isPrecond = True
            else:
                assert (isPrecond is not None)
                if isPrecond:
                    preconds.append(word)
                else:
                    premises.append(word)

        # Get the conclusion
        conclusion = m.group('conclusion')
        macroFile.write (rule2latex(rulename, preconds, premises, conclusion))

    # We also define a macro which shows all rules of this section.

    macroFile.write ("%%%%%%\n")
    macroFile.write (Template(r"\newcommand{\${title}Rules}{%").substitute({
        'title' : title
    }))
    for rule in rules:
        rulename = rule[0]
        macroFile.write ("\n")
        macroFile.write(Template(r"""\begin{equation}
\label{rule:$ruleName}
\show$ruleName
\tag{\ruleFont{$ruleName}}
\end{equation}"""
        ).substitute({
            'ruleName' : ruleName(rulename),
        }))
    macroFile.write ('}\n\n')

    # And another one that is paranoid

    macroFile.write ("%%%%%%\n")
    macroFile.write (Template(r"\newcommand{\${title}RulesParanoid}{%").substitute({
        'title' : title
    }))
    for rule in rules:
        rulename = rule[0]
        macroFile.write ("\n")
        macroFile.write(Template(r"""\begin{equation}
\label{rule-paranoid:$ruleName}
\show${ruleName}Paranoid
\tag{\ruleFont{$ruleName}}
\end{equation}"""
        ).substitute({
            'ruleName' : ruleName(rulename),
        }))
    macroFile.write ('}\n\n')

### MAIN PROGRAM

opts = argparse.ArgumentParser(description='Generate LaTeX from inference rules.')
opts.add_argument('--output', default='tt.tex', help='save rule macros in this file')
opts.add_argument('coqfile', help='the Coq file containing the rules.')

args = opts.parse_args()

# load the source file
with open(args.coqfile, "r") as f:
    src = f.read()

# remove prelude and split into sections.
sections = re.split(r'Inductive', src, 1)[1]
sections = re.split(r'Inductive|with\b', sections)

# Write out the file with macro definitions
with open(args.output, 'w') as macroFile:
    # Determine the version of the rules
    version = subprocess.check_output(['git', 'describe', '--always', '--long']).strip()
    macroFile.write(Template(r'\newcommand{\rulesVersion}{$version}').substitute({
        'version' : version
    }))
    macroFile.write("\n")
    # Process each section separately.
    for sect in sections:
        m = re.match(r'^\s+(\w+)\s+:', sect) or die ("could not find section title")
        title = m.group(1)
        section(macroFile, title, sect)

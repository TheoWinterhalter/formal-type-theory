#!/usr/bin/env python
import sys
import re
import argparse
import subprocess
import logging
from string import Template

configurations = {
    'extensional' : 'extensional',
    'simpleproduct' : 'simpleproduct',
    'prodeta' : 'prodeta',
    'universe' : 'universe',
    'withprop' : 'withprop',
    'identitytype' : 'identitytype',
    'withj' : 'withj',
    'withempty' : 'withempty',
    'withunit' : 'withunit',
    'withbool' : 'withbool',
    'withpi' : 'withpi',
}

# The identifiers which are translated to macros, with the given number of arguments
macros = {
    # Convert boring names to more mathematical ones
    'G' : (0, 'Gamma'),
    'D' : (0, 'Delta'),
    'E' : (0, 'Theta'),
    'l' : (0, 'ell'),
    'sb' : (0, 'sigma'),
    'sbs' : (0, 'sigma'),
    'sbt' : (0, 'tau'),
    'sbr' : (0, 'rho'),

    # Judgment forms
    'isctx' : (1, 'isctx'),
    'istype' : (2, 'istype'),
    'isterm' : (3, 'isterm'),
    'issubst' : (3, 'issubst'),
    'eqtype' : (3, 'eqtype'),
    'eqterm' : (4, 'eqterm'),
    'eqctx' : (2, 'eqctx'),
    'eqsubst' : (4, 'eqsubst'),

    # Variables
    'var' : (1, 'var'),
    'S' : (1, 'suc'),

    # Substitution
    'Subst' : (2, 'Subst'),
    'subst' : (2, 'subst'),
    'sbzero' : (2, 'sbzero'),
    'sbweak' : (1, 'sbweak'),
    'sbshift' : (2, 'sbshift'),
    'sbid' : (0, 'sbid'),
    'sbcomp' : (2, 'sbcomp'),
    'sbterminal' : (0, 'sbterminal'),

    # Contexts
    'ctxempty' : (0, 'ctxempty'),
    'ctxextend' : (2, 'ctxextend'),

    # Products
    'Prod' : (2, 'Prod'),
    'lam' : (3, 'lam'),
    'app' : (4, 'app'),

    # Identity types
    'Id' : (3, 'Id'),
    'refl' : (2, 'refl'),
    'j' : (6, 'J'),

    # Simple products
    'SimProd' : (2, 'SimProd'),
    'pair' : (4, 'pair'),
    'proj1' : (3, 'projOne'),
    'proj2' : (3, 'projTwo'),

    # Empty
    'Empty' : (0, 'Empty'),
    'exfalso' : (2, 'exfalso'),

    # Unit
    'Unit' : (0, 'Unit'),
    'unit' : (0, 'unit'),

    # Bool
    'Bool' : (0, 'Bool'),
    'true' : (0, 'true'),
    'false' : (0, 'false'),
    'cond' : (4, 'cond'),

    # Universes
    'El' : (2, 'El'),
    'Uni' : (1, 'Univ'),
    'prop' : (0, 'propLevel'),
    'uni' : (1, 'univ'), # injection from nat to universe levels
    'uniProd' : (4, 'uniProd'),
    'uniId' : (4, 'uniId'),
    'uniEmpty' : (1, 'uniEmpty'),
    'uniUnit' : (1, 'uniUnit'),
    'uniBool' : (1, 'uniBool'),
    'uniSimProd' : (4, 'uniSimProd'),
    'uniUni' : (1, 'uniUni')
}

def is_macro(k):
    return (k in macros)

def the_arity(k):
    if is_macro(k):
        return macros[k][0]
    else:
        return None

def the_macro(k):
    if is_macro(k):
        return macros[k][1]
    else:
        return None

def embrace(s):
    return '{' + s + '}'

def subscribe(t, s):
    return "{0}_{{{1}}}".format(t, s) if s else t


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

class Ident():
    def __init__(self, keyword):
        m = re.match(r'^(.*?)(\d+)$', keyword)
        if m and not (keyword in macros):
            self.keyword = m.group(1)
            self.subscript = m.group(2)
        else:
            self.keyword = keyword
            self.subscript = None

    def __str__(self):
        s = self.keyword if not is_macro(self.keyword) else "{{\\{0}}}".format(the_macro(self.keyword))
        if self.subscript is not None:
            s = subscribe(s, self.subscript)
        return s

    def __repr__(self):
        return str(self)

    def makeApp(self, args):
        if len(args) == 0:
            return self
        else:
            return Application(self, args)

    def is_macro(self):
        return (is_macro(self.keyword) and the_arity(self.keyword) > 0)

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
                assert False, ("macro {0} expects {1} arguments but got {2} ({3})".format(m, arity, len(self.args), self.args))
            else:
                return "\\{0}{1}".format(m, "".join([embrace(str(a)) for a in self.args ]))
        else:
            return "{0}\, {1}".format(str(self.head), "\, ".join(map(str, self.args)))

    def __repr__(self):
        return str(self)

def parseSimple(tok):
    if tok.peek() == '(':
        tok.pop()
        e = parseApply(tok)
        assert (tok.pop() == ')'), ("parsing: expected )".format(c))
        return e
    elif tok.peek() is not None and bool(re.match(r'\w+', tok.peek())):
        t = tok.pop()
        ob =  Ident(t)
        return ob
    else:
        return None

def parseApply(tok):
    head = parseSimple(tok)
    assert (head is not None), "empty head in parseApply"
    args = []
    t = parseSimple(tok)
    while t is not None:
        args.append(t)
        t = parseSimple(tok)
    return head.makeApp(args)

def parseExpr(tok):
    logging.debug ("   parsing expression {0}".format(tok))
    e = parseApply(tok)
    assert (tok.pop() is None), "premature end"
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
r"""
%%%% RULE: $ruleName

\newcommand{\rule$ruleName}{\ruleRef{$ruleName}{rule:$ruleName}}

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
            r'^\s*\|\s+'                          # the beginning of a rule
            r'(?P<rulename>[a-zA-Z_]+)\s*:\s*$'   # rule name
            r'\s*(?P<ruleconfigs>(?:\w+\s+)*)\s*' # configuration options
            r'\s*rule\s*'                         # header
            r'(?P<rulebody>.*?)'                  # rule body
            r'endrule',                           # footer
            src,
            re.DOTALL + re.MULTILINE)

    for rule in rules:
        rulename = rule[0]
        logging.debug ("parsing rule {0}".format(rulename))
        rulebody = rule[2]
        m = re.match(
            r'^(\s*parameters:.*?,)?'                 # optional parameters
            r'(?P<premises>.*?)'                      # premises
            r'conclusion:\s*(?P<conclusion>.*)\s*$',  # the rest is the rule
            rulebody,
            re.DOTALL)
        assert m, ("Failed to parse rule {0} whose body is:\n{1}".format(rulename, rulebody))

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
        configs = re.split('\s+', rule[1])
        if len(configs) > 0: configs.pop()
        if len(configs) == 0:
            configurationOptions = ""
        else:
            configurationOptions = []
            for config in configs:
                #assert (config in configurations), "unknown configuration option {0}".format(config)
                #configurationOptions.append("\textsc{{{0}}}".format(configurations[config]))
                configurationOptions.append("\\textsc{{{0}}}".format(config))
            configurationOptions = "({0})".format(", ".join(configurationOptions))
        macroFile.write ("\n")
        macroFile.write(Template(r"""\noindent
$$\ruleFont{$ruleName}$$ \configParameters{$configurationOptions}
\label{rule:$ruleName}
\begin{equation*}
\show$ruleName
\end{equation*}"""
        ).substitute({
            'ruleName' : ruleName(rulename),
            'configurationOptions' : configurationOptions,
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
        macroFile.write(Template(r"""\noindent
$$\ruleFont{$ruleName}$$ \configParameters{$configurationOptions}
\label{rule:$ruleName}
\begin{equation*}
\show${ruleName}Paranoid
\end{equation*}"""
        ).substitute({
            'ruleName' : ruleName(rulename),
            'configurationOptions' : configurationOptions,
        }))
    macroFile.write ('}\n\n')

### MAIN PROGRAM

opts = argparse.ArgumentParser(description='Generate LaTeX from inference rules.')
opts.add_argument('--output', default='tt.tex', help='save rule macros in this file')
opts.add_argument('coqfile', help='the Coq file containing the rules.')
opts.add_argument('--debug', action='store_true', default=False, help='print debugging info')
args = opts.parse_args()

if args.debug:
    logging.basicConfig(level=logging.DEBUG)

# load the source file and remove all comments (NESTED COMMENTS ARE NOT ALLOWED)
with open(args.coqfile, "r") as f:
    src = f.read()
    src = re.sub(r'\(\*.*?\*\)', '', src)

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
        m = re.match(r'^\s+(\w+)\s+:', sect)
        assert m, "could not find section title"
        title = m.group(1)
        section(macroFile, title, sect)

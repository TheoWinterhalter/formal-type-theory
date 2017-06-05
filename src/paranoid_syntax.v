(* Paranoid Syntax

   We propose an implementation of syntax that corresponds to the syntax with
   which this library was designed at first.
   It features all the specifics of the language as mutual inductive types.

   This includes explicit substitutions, seperate syntaxes for types and terms,
   optional Tarski universes and so on...

   This syntax is still configurable. For instance, if you decide not to have
   the Unit type as part of your theory, it will still be part of the syntax,
   but you won't be able to derive that [Γ ⊢ Unit] type or [Γ ⊢ unit : Unit].
*)

Require config.

Section ParanoidSyntax.

(* Universe levels *)
Inductive level : Type :=
| uni : nat -> level
| prop : level
.

Inductive context : Type :=
     | ctxempty : context
     | ctxextend : context -> type -> context

with type : Type :=
     | Prod : type -> type -> type
     | Id : type -> term -> term -> type
     | Subst : type -> substitution -> type
     | Empty : type
     | Unit : type
     | Bool : type
     | SimProd : type -> type -> type
     | Uni : level -> type
     | El : level -> term -> type

with term : Type :=
     | var : nat -> term
     | lam : type -> type -> term -> term
     | app : term -> type -> type -> term -> term
     | refl : type -> term -> term
     | j : type -> term -> type -> term -> term -> term -> term
     | subst : term -> substitution -> term
     | exfalso : type -> term -> term
     | unit : term
     | true : term
     | false : term
     | cond : type -> term -> term -> term -> term
     | pair : type -> type -> term -> term -> term
     | proj1 : type -> type -> term -> term
     | proj2 : type -> type -> term -> term
     | uniProd : level -> level -> term -> term -> term
     | uniId : level -> term -> term -> term -> term
     | uniEmpty : level -> term
     | uniUnit : level -> term
     | uniBool : nat -> term
     | uniSimProd : level -> level -> term -> term -> term
     | uniUni : level -> term

with substitution : Type :=
     | sbzero : type -> term -> substitution
     | sbweak : type -> substitution
     | sbshift : type -> substitution -> substitution
     | sbid : substitution
     | sbcomp : substitution -> substitution -> substitution
.

Definition exactly : forall {F A}, A -> config.Flag F -> A.
Proof.
  intros F A a f.
  exact a.
Defined.

Local Instance Syntax : config.Syntax := {|
  config.context      := context ;
  config.type         := type ;
  config.term         := term ;
  config.substitution := substitution ;

  config.ctxempty  := ctxempty ;
  config.ctxextend := ctxextend ;

  config.Id    := Id ;
  config.Subst := Subst ;

  config.var   := var ;
  config.refl  := refl ;
  config.subst := subst ;

  config.sbzero  := sbzero ;
  config.sbweak  := sbweak ;
  config.sbshift := sbshift ;
  config.sbid    := sbid ;
  config.sbcomp  := sbcomp
|}.

Context {ConfigPrecond : config.Precond}.
Context {ConfigReflection : config.Reflection}.

Context {simpleproductsFlag : Type}.
Local Instance SimpleProducts : config.SimpleProducts := {|
  config.simpleproductsFlag := simpleproductsFlag ;

  config.SimProd := exactly SimProd ;

  config.pair  := exactly pair  ;
  config.proj1 := exactly proj1 ;
  config.proj2 := exactly proj2
|}.

Context {ConfigProdEta : config.ProdEta}.

Local Instance UniverseLevels : config.UniverseLevels := {|
  config.level := level
|}.

Context {universesFlag : Type}.
Local Instance Universes : config.Universes := {|
  config.universesFlag := universesFlag ;

  config.uni := exactly uni ;

  config.Uni := exactly Uni ;
  config.El  := exactly El  ;

  config.uniUni := exactly uniUni
|}.

Context {withpropFlag : Type}.
Local Instance WithProp : config.WithProp := {|
  config.withpropFlag := withpropFlag ;

  config.prop := exactly prop
|}.

Context {withjFlag : Type}.
Local Instance WithJ : config.WithJ := {|
  config.withjFlag := withjFlag ;

  config.j := exactly j
|}.

Context {withemptyFlag : Type}.
Local Instance WithEmpty : config.WithEmpty := {|
  config.withemptyFlag := withemptyFlag ;

  config.Empty := exactly Empty ;

  config.exfalso := exactly exfalso
|}.

Context {withunitFlag : Type}.
Local Instance WithUnit : config.WithUnit := {|
  config.withunitFlag := withunitFlag ;

  config.Unit := exactly Unit ;

  config.unit := exactly unit
|}.

Context {withboolFlag : Type}.
Local Instance WithBool : config.WithBool := {|
  config.withboolFlag := withboolFlag ;

  config.Bool := exactly Bool ;

  config.true  := exactly true  ;
  config.false := exactly false ;
  config.cond  := exactly cond
|}.

Context {withpiFlag : Type}.
Local Instance WithPi : config.WithPi := {|
  config.withpiFlag := withpiFlag ;

  config.Prod := exactly Prod ;

  config.lam := exactly lam ;
  config.app := exactly app
|}.

Local Instance UniProd : config.UniProd := {|
  config.uniProd := exactly (exactly uniProd)
|}.

Local Instance UniId : config.UniId := {|
  (* config.uniId := exactly (exactly uniId) *)
  config.uniId := exactly uniId
|}.

Local Instance UniEmpty : config.UniEmpty := {|
  config.uniEmpty := exactly (exactly uniEmpty)
|}.

Local Instance UniUnit : config.UniUnit := {|
  config.uniUnit := exactly (exactly uniUnit)
|}.

Local Instance UniBool : config.UniBool := {|
  config.uniBool := exactly (exactly uniBool)
|}.

Local Instance UniSimProd : config.UniSimProd := {|
  config.uniSimProd := exactly (exactly uniSimProd)
|}.

End ParanoidSyntax.

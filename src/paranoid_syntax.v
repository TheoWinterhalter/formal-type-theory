(* Paranoid Syntax

   We propose an implementation of syntax that corresponds to the syntax with
   which this library was designed at first.
   It features all the specifics of the language as mutual inductive types.

   This includes explicit substitutions, seperate syntaxes for types and terms,
   optional Tarski universes and so on...

   Thi syntax is still configurable. For instance, if you decide not to have
   the Unit type as part of your theory, it will still be part of the syntax,
   but you won't be able to derive that [Γ ⊢ Unit] type or [Γ ⊢ unit : Unit].
*)

Require config.

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
     | sbcomp : substitution -> substitution -> substitution.

Definition Arrow (A B : type) : type :=
  Prod A (Subst B (sbweak A)).

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

Local Instance SimpleProducts : config.SimpleProducts := {|
  (* config.simpleproductsFlag := ? *)

  config.SimProd := exactly SimProd ;

  config.pair  := exactly pair  ;
  config.proj1 := exactly proj1 ;
  config.proj2 := exactly proj2
|}.

Context {ConfigProdEta : config.ProdEta}.

Local Instance UniverseLevels : config.UniverseLevels := {|
  config.level := level
|}.

Local Instance Universes : config.Universes := {|
  config.uni := exactly uni ;

  config.Uni := exactly Uni ;
  config.El  := exactly El  ;

  config.uniUni := exactly uniUni
|}.

Local Instance WithProp : config.WithProp := {|
  config.prop := exactly prop
|}.

(* TODO BELOW! *)
Context {ConfigWithJ : config.WithJ}.
Context {ConfigEmpty : config.WithEmpty}.
Context {ConfigUnit : config.WithUnit}.
Context {ConfigBool : config.WithBool}.
Context {ConfigPi : config.WithPi}.
Context {ConfigUniProd : config.UniProd}.
Context {ConfigUniId : config.UniId}.
Context {ConfigUniEmpty : config.UniEmpty}.
Context {ConfigUniUnit : config.UniUnit}.
Context {ConfigUniBool : config.UniBool}.
Context {ConfigUniSimProd : config.UniSimProd}.

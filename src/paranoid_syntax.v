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

Require config syntax tt.

Section ParanoidSyntax.

Context `{configPrecond : config.Precond}.
Context `{configReflection : config.Reflection}.
Context `{configSimpleProducts : config.SimpleProducts}.
Context `{configProdEta : config.ProdEta}.
Context `{configUniverses : config.Universes}.
Context `{configWithProp : config.WithProp}.
Context `{configId : config.IdentityTypes}.
Context `{configWithJ : config.WithJ}.
Context `{configEmpty : config.WithEmpty}.
Context `{configUnit : config.WithUnit}.
Context `{configBool : config.WithBool}.
Context `{configPi : config.WithPi}.

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
     | Uni : syntax.level -> type
     | El : syntax.level -> term -> type

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
     | uniProd : syntax.level -> syntax.level -> term -> term -> term
     | uniId : syntax.level -> term -> term -> term -> term
     | uniEmpty : syntax.level -> term
     | uniUnit : syntax.level -> term
     | uniBool : nat -> term
     | uniSimProd : syntax.level -> syntax.level -> term -> term -> term
     | uniUni : syntax.level -> term

with substitution : Type :=
     | sbzero : type -> term -> substitution
     | sbweak : type -> substitution
     | sbshift : type -> substitution -> substitution
     | sbid : substitution
     | sbcomp : substitution -> substitution -> substitution
.

Local Instance Syntax : syntax.Syntax := {|
  syntax.context      := context ;
  syntax.type         := type ;
  syntax.term         := term ;
  syntax.substitution := substitution ;

  syntax.ctxempty  := ctxempty ;
  syntax.ctxextend := ctxextend ;

  syntax.Prod    := Prod ;
  syntax.Id      := Id ;
  syntax.Subst   := Subst ;
  syntax.Empty   := Empty ;
  syntax.Unit    := Unit ;
  syntax.Bool    := Bool ;
  syntax.SimProd := SimProd ;
  syntax.Uni     := Uni ;
  syntax.El      := El  ;

  syntax.var        := var ;
  syntax.lam        := lam ;
  syntax.app        := app ;
  syntax.refl       := refl ;
  syntax.j          := j ;
  syntax.subst      := subst ;
  syntax.exfalso    := exfalso ;
  syntax.unit       := unit ;
  syntax.true       := true  ;
  syntax.false      := false ;
  syntax.cond       := cond ;
  syntax.pair       := pair ;
  syntax.proj1      := proj1 ;
  syntax.proj2      := proj2 ;
  syntax.uniProd    := uniProd ;
  (* syntax.uniId      := uniId ; *)
  syntax.uniId      := uniId ;
  syntax.uniEmpty   := uniEmpty ;
  syntax.uniUnit    := uniUnit ;
  syntax.uniBool    := uniBool ;
  syntax.uniSimProd := uniSimProd ;
  syntax.uniUni     := uniUni ;

  syntax.sbzero  := sbzero ;
  syntax.sbweak  := sbweak ;
  syntax.sbshift := sbshift ;
  syntax.sbid    := sbid ;
  syntax.sbcomp  := sbcomp
|}.

Definition isctx := tt.isctx.
Definition issubst := tt.issubst.
Definition istype := tt.istype.
Definition isterm := tt.isterm.
Definition eqctx := tt.eqctx.
Definition eqsubst := tt.eqsubst.
Definition eqtype := tt.eqtype.
Definition eqterm := tt.eqterm.

End ParanoidSyntax.
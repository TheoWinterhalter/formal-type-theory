(* Fully annotated syntax

   A specific syntax in which terms are explicitly tagged with types.
   This syntax is defined inductively, so we can run inversion tactics on it,
   which is used in showing uniqueness of typing, for example.
*)

Require tt.

Section AnnotatedSyntax.

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
     | BinaryProd : type -> type -> type
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
     | uniBinaryProd : syntax.level -> syntax.level -> term -> term -> term
     | uniUni : syntax.level -> term

with substitution : Type :=
     | sbzero : type -> term -> substitution
     | sbweak : type -> substitution
     | sbshift : type -> substitution -> substitution
     | sbid : substitution
     | sbcomp : substitution -> substitution -> substitution
     | sbterminal : substitution
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
  syntax.BinaryProd := BinaryProd ;
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
  syntax.uniId      := uniId ;
  syntax.uniEmpty   := uniEmpty ;
  syntax.uniUnit    := uniUnit ;
  syntax.uniBool    := uniBool ;
  syntax.uniBinaryProd := uniBinaryProd ;
  syntax.uniUni     := uniUni ;

  syntax.sbzero     := sbzero ;
  syntax.sbweak     := sbweak ;
  syntax.sbshift    := sbshift ;
  syntax.sbid       := sbid ;
  syntax.sbcomp     := sbcomp ;
  syntax.sbterminal := sbterminal
|}.

End AnnotatedSyntax.

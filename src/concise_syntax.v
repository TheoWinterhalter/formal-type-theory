(* Concise syntax

   A specific syntax that avoids annotations as much as possible all the while
   computing and featuring no distinction between types and terms and Russel
   universes.

   It is meant as a dual / other extreme to annotated syntax.
*)

Require tt.

Section ConciseSyntax.

Inductive context : Type :=
     | ctxempty : context
     | ctxextend : context -> term -> context

with term : Type :=
     (* Types *)
     | Prod : term -> term -> term
     | Id : term -> term -> term -> term
     | Empty : term
     | Unit : term
     | Bool : term
     | BinaryProd : term -> term -> term
     | Uni : syntax.level -> term
     (* Terms *)
     | var : nat -> term
     | lam : term -> term -> term
     | app : term -> term -> term
     | refl : term -> term
     | j : term -> term -> term -> term -> term -> term -> term
     | subst : term -> substitution -> term
     | exfalso : term -> term -> term
     | unit : term
     | true : term
     | false : term
     | cond : term -> term -> term -> term -> term
     | pair : term -> term -> term -> term -> term
     | proj1 : term -> term -> term -> term
     | proj2 : term -> term -> term -> term

with substitution : Type :=
     | sbzero : term -> term -> substitution
     | sbweak : term -> substitution
     | sbshift : term -> substitution -> substitution
     | sbid : substitution
     | sbcomp : substitution -> substitution -> substitution
     | sbterminal : substitution
.

Local Instance Syntax : syntax.Syntax := {|
  syntax.context      := context ;
  syntax.type         := term ;
  syntax.term         := term ;
  syntax.substitution := substitution ;

  syntax.ctxempty  := ctxempty ;
  syntax.ctxextend := ctxextend ;

  syntax.Prod       := Prod ;
  syntax.Id         := Id ;
  syntax.Subst      := subst ;
  syntax.Empty      := Empty ;
  syntax.Unit       := Unit ;
  syntax.Bool       := Bool ;
  syntax.BinaryProd := BinaryProd ;
  syntax.Uni        := Uni ;
  syntax.El i T     := T ;

  syntax.var n                 := var n ;
  syntax.lam A B t             := lam A t ;
  syntax.app u A B v           := app u v ;
  syntax.refl A u              := refl u ;
  syntax.j A u C w v p         := j A u C w v p ;
  syntax.subst u sbs           := subst u sbs ;
  syntax.exfalso A u           := exfalso A u ;
  syntax.unit                  := unit ;
  syntax.true                  := true  ;
  syntax.false                 := false ;
  syntax.cond C u v w          := cond C u v w ;
  syntax.pair A B u v          := pair A B u v ;
  syntax.proj1 A B p           := proj1 A B p ;
  syntax.proj2 A B p           := proj2 A B p ;
  syntax.uniProd i j A B       := Prod A B ;
  syntax.uniId i A u v         := Id A u v ;
  syntax.uniEmpty i            := Empty ;
  syntax.uniUnit i             := Unit ;
  syntax.uniBool i             := Bool ;
  syntax.uniBinaryProd i j A B := BinaryProd A B ;
  syntax.uniUni i              := Uni i ;

  syntax.sbzero     := sbzero ;
  syntax.sbweak     := sbweak ;
  syntax.sbshift    := sbshift ;
  syntax.sbid       := sbid ;
  syntax.sbcomp     := sbcomp ;
  syntax.sbterminal := sbterminal
|}.

End ConciseSyntax.

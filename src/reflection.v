(* Translating away reflection *)

Require config.
Require Import config_tactics.
Require Import syntax.
Require Import tt.
Require Import checking_tactics.

(* Syntax *)
Module S.

Section AnnotatedSyntax.

Inductive context : Type :=
     | ctxempty : context
     | ctxextend : context -> term -> context

with term : Type :=
     | Prod : term -> term -> term
     | Id : term -> term -> term -> term
     | BinaryProd : term -> term -> term
     | Uni : syntax.level -> term
     | var : nat -> term
     | lam : term -> term -> term -> term
     | app : term -> term -> term -> term -> term
     | refl : term -> term -> term
     | j : term -> term -> term -> term -> term -> term -> term
     | subst : term -> substitution -> term
     | pair : term -> term -> term -> term -> term
     | proj1 : term -> term -> term -> term
     | proj2 : term -> term -> term -> term

with substitution : Type :=
     | sbzero : term -> term -> substitution
     | sbweak : term -> substitution
     | sbshift : term -> substitution -> substitution
     | sbid : substitution
     | sbcomp : substitution -> substitution -> substitution
.

Definition unimplemented : term := var 0.

Global Instance Syntax : syntax.Syntax := {|
  syntax.context      := context ;
  syntax.type         := term ;
  syntax.term         := term ;
  syntax.substitution := substitution ;

  syntax.ctxempty  := ctxempty ;
  syntax.ctxextend := ctxextend ;

  syntax.Prod    := Prod ;
  syntax.Id      := Id ;
  syntax.Subst   := subst ;
  syntax.Empty   := unimplemented ;
  syntax.Unit    := unimplemented ;
  syntax.Bool    := unimplemented ;
  syntax.BinaryProd := BinaryProd ;
  syntax.Uni     := Uni ;
  syntax.El l a  := a ;

  syntax.var        := var ;
  syntax.lam        := lam ;
  syntax.app        := app ;
  syntax.refl       := refl ;
  syntax.j          := j ;
  syntax.subst      := subst ;
  syntax.exfalso    := fun _ _ => unimplemented ;
  syntax.unit       := unimplemented ;
  syntax.true       := unimplemented  ;
  syntax.false      := unimplemented ;
  syntax.cond       := fun _ _ _ _ => unimplemented ;
  syntax.pair       := pair ;
  syntax.proj1      := proj1 ;
  syntax.proj2      := proj2 ;
  syntax.uniProd l l' := Prod ;
  syntax.uniId l    := Id ;
  syntax.uniEmpty   := fun _ => unimplemented ;
  syntax.uniUnit    := fun _ => unimplemented ;
  syntax.uniBool    := fun _ => unimplemented ;
  syntax.uniBinaryProd l l' := BinaryProd ;
  syntax.uniUni     := Uni ;

  syntax.sbzero  := sbzero ;
  syntax.sbweak  := sbweak ;
  syntax.sbshift := sbshift ;
  syntax.sbid    := sbid ;
  syntax.sbcomp  := sbcomp
|}.

End AnnotatedSyntax.

End S.

(* Source type theory *)
Module Stt.

  Section Stt.

  Local Instance havePrecondition : config.Precondition
    := {| config.flagPrecondition := config.Yes |}.
  Local Instance haveReflection : config.Reflection
    := {| config.flagReflection := config.Yes |}.
  Local Instance haveBinaryProdType : config.BinaryProdType
    := {| config.flagBinaryProdType := config.Yes |}.
  Local Instance noProdEta : config.ProdEta
    := {| config.flagProdEta := config.No |}.
  Local Instance haveUniverses : config.Universes
    := {| config.flagUniverses := config.Yes |}.
  Local Instance noPropType : config.PropType
    := {| config.flagPropType := config.No |}.
  Local Instance haveIdType : config.IdType
    := {| config.flagIdType := config.Yes |}.
  Local Instance haveIdEliminator : config.IdEliminator
    := {| config.flagIdEliminator := config.Yes |}.
  Local Instance noEmptyType : config.EmptyType
    := {| config.flagEmptyType := config.No |}.
  Local Instance noUnitType : config.UnitType
    := {| config.flagUnitType := config.No |}.
  Local Instance noBoolType : config.BoolType
    := {| config.flagBoolType := config.No |}.
  Local Instance haveProdType : config.ProdType
    := {| config.flagProdType := config.Yes |}.

  Definition isctx   := isctx.
  Definition issubst := issubst.
  Definition istype  := istype.
  Definition isterm  := isterm.
  Definition eqctx   := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype  := eqtype.
  Definition eqterm  := eqterm.

  End Stt.

End Stt.

(* Target type theory *)
Module Ttt.

  Section Ttt.

  Local Instance noPrecondition : config.Precondition
    := {| config.flagPrecondition := config.No |}.
  Local Instance noReflection : config.Reflection
    := {| config.flagReflection := config.No |}.
  Local Instance haveBinaryProdType : config.BinaryProdType
    := {| config.flagBinaryProdType := config.Yes |}.
  Local Instance noProdEta : config.ProdEta
    := {| config.flagProdEta := config.No |}.
  Local Instance haveUniverses : config.Universes
    := {| config.flagUniverses := config.Yes |}.
  Local Instance noPropType : config.PropType
    := {| config.flagPropType := config.No |}.
  Local Instance haveIdType : config.IdType
    := {| config.flagIdType := config.Yes |}.
  Local Instance haveIdEliminator : config.IdEliminator
    := {| config.flagIdEliminator := config.Yes |}.
  Local Instance noEmptyType : config.EmptyType
    := {| config.flagEmptyType := config.No |}.
  Local Instance noUnitType : config.UnitType
    := {| config.flagUnitType := config.No |}.
  Local Instance noBoolType : config.BoolType
    := {| config.flagBoolType := config.No |}.
  Local Instance haveProdType : config.ProdType
    := {| config.flagProdType := config.Yes |}.

  Definition isctx   := isctx.
  Definition issubst := issubst.
  Definition istype  := istype.
  Definition isterm  := isterm.
  Definition eqctx   := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype  := eqtype.
  Definition eqterm  := eqterm.

  Axiom uip : term -> term -> term.
  Axiom TermUIP :
    forall {Γ A u v p q},
      isterm Γ p (Id A u v) ->
      isterm Γ q (Id A u v) ->
      isterm Γ (uip p q) (Id (Id A u v) p q).

  Axiom funext : term -> term.
  Axiom TermFunext :
    forall {Γ A B f g e},
      isterm Γ f (Prod A B) ->
      isterm Γ g (Prod A B) ->
      isterm
        Γ
        e
        (Prod
           A
           (Id
              B
              (app
                 (subst f (sbweak A))
                 (subst A (sbweak A))
                 (subst B (sbweak A))
                 (var 0))
              (app
                 (subst g (sbweak A))
                 (subst A (sbweak A))
                 (subst B (sbweak A))
                 (var 0)))).

  End Ttt.

End Ttt.

Section Translation.

(* Proving uniqueness of typing and inversion are going to be challenges.
   Weakening is merely an application of the right substitution.
 *)
Lemma uniqueness :
  forall {Γ u T1 T2},
    Ttt.isterm Γ u T1 ->
    Ttt.isterm Γ u T2 ->
    Ttt.eqtype Γ T1 T2.
Admitted.

(* We define transport as an extra symbol *)
Context {transport : nat -> term -> term -> term -> term -> term}.
Context {
  TermTransport :
    forall {Γ n T1 T2 p t},
      Ttt.isctx Γ ->
      Ttt.isterm Γ T1 (Uni (uni n)) ->
      Ttt.isterm Γ T2 (Uni (uni n)) ->
      Ttt.isterm Γ p (Id (Uni (uni n)) T1 T2) ->
      Ttt.isterm Γ t T1 ->
      Ttt.isterm Γ (transport n T1 T2 p t) T2
}.

End Translation.

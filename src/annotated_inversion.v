(* Annotated syntax inversion

   The purpose of this file is to provide the inversion lemmata that are
   required by sanity on annotated syntax.
   These lemmata are proven only in the case of paranoid rules.
*)

Require config syntax.
Require Import tt.
Require inversion.
Require Import annotated_syntax.
Require Import config_tactics.

Section AnnotatedSyntaxInversion.

Local Instance hasPrecondition : config.Precondition := {|
  config.flagPrecondition := config.Yes
|}.
Context `{configReflection : config.Reflection}.
Context `{configBinaryProdType : config.BinaryProdType}.
Context `{configProdEta : config.ProdEta}.
Context `{configUniverses : config.Universes}.
Context `{configPropType : config.PropType}.
Context `{configIdType : config.IdType}.
Context `{configIdEliminator : config.IdEliminator}.
Context `{configEmptyType : config.EmptyType}.
Context `{configUnitType : config.UnitType}.
Context `{configBool : config.WithBool}.
Context `{configProdType : config.ProdType}.

Local Existing Instance annotated_syntax.Syntax.

Definition CtxExtendInversion G A (H : isctx (ctxextend G A)) :
  isctx G * istype G A.
Proof.
  config inversion H. easy.
Defined.

Fixpoint TyIdInversion G A u v (H : istype G (Id A u v)) {struct H} :
  isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  inversion H ; doConfig.

  - { split ; [(split ; [split | idtac]) | idtac].

      - assumption.
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply TyIdInversion with (u := u) (v := v).
      - apply @tt.TermCtxConv with (G := G0) ; auto.
        + now apply TyIdInversion with (u := u) (v:= v).
        + now config apply TyIdInversion with (u := u) (v:= v).
      - apply @tt.TermCtxConv with (G := G0) ; auto.
        + now apply TyIdInversion with (u := u) (v:= v).
        + now config apply TyIdInversion with (u := u) (v:= v).
    }

  - { split ; [(split ; [split | idtac]) | idtac].
      - assumption.
      - assumption.
      - assumption.
      - assumption.
    }

Defined.

Fixpoint TyProdInversion G A B (H : istype G (Prod A B)) {struct H} :
  isctx G * istype G A * istype (ctxextend G A) B.
Proof.
  inversion H ; doConfig.

  - { split ; [ split | idtac ].
      - assumption.
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TyProdInversion G0 A B).
      - apply @tt.TyCtxConv with (G := ctxextend G0 A).
        + now apply (TyProdInversion G0 A B).
        + apply @tt.EqCtxExtend ; auto.
          * now capply (TyProdInversion G0 A B).
          * now capply (TyProdInversion G0 A B).
          * capply @tt.EqTyRefl ; auto.
            now apply (TyProdInversion G0 A B).
        + capply @tt.CtxExtend ; auto.
          now apply (TyProdInversion G0 A B).
        + capply @tt.CtxExtend.
          * assumption.
          * apply @tt.TyCtxConv with (G := G0) ; auto.
            now apply (TyProdInversion G0 A B).
    }

  - { split ; [ split | idtac ].
      - assumption.
      - assumption.
      - assumption.
    }
Defined.

Fixpoint TyBinaryProdInversion G A B (H : istype G (BinaryProd A B)) {struct H} :
  isctx G * istype G A * istype G B.
Proof.
  inversion H ; doConfig.

  - { split ; [ split | .. ].
      - assumption.
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TyBinaryProdInversion G0 A B).
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TyBinaryProdInversion G0 A B).
    }

  - { split ; [ split | .. ] ; assumption. }
Defined.

Local Instance LocSyntax : syntax.Syntax := Syntax.

Local Instance haveCtxExtendInversion : inversion.HaveCtxExtendInversion
  := {| inversion.CtxExtendInversion := CtxExtendInversion |}.

Local Instance haveTyIdInversion : inversion.HaveTyIdInversion
  := {| inversion.TyIdInversion := TyIdInversion |}.

Local Instance haveTyProdInversion : inversion.HaveTyProdInversion
  := {| inversion.TyProdInversion := TyProdInversion |}.

Local Instance haveTyBinaryProdInversion : inversion.HaveTyBinaryProdInversion
  := {| inversion.TyBinaryProdInversion := TyBinaryProdInversion |}.

End AnnotatedSyntaxInversion.

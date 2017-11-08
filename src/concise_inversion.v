(* Concise syntax inversion

   The purpose of this file is to provide the inversion lemmata that are
   required by sanity on concise syntax.
   These lemmata are proven only in the case of paranoid rules.
*)

Require config syntax.
Require Import tt.
Require inversion.
Require Import concise_syntax.
Require Import config_tactics.

Section ConciseSyntaxInversion.

Local Instance hasPrecond : config.Precond := {|
  config.precondFlag := config.Yes
|}.
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

Local Existing Instance concise_syntax.Syntax.

Definition CtxExtendInversion G A (H : isctx (ctxextend G A)) :
  isctx G * istype G A.
Proof.
  config inversion H. easy.
Defined.

Fixpoint TermIdInversion `{ fl : config.universesFlag } G A u v U
         (H : isterm G (Id A u v) U) {struct H} :
  forall {l}, eqtype G U (Uni l) ->
         isctx G * istype G A * isterm G A U * isterm G u A * isterm G v A.
Proof.
  intros l h.
  inversion H ; doConfig.

  - { assert (eq : eqtype G A0 (Uni l)).
      { ceapply EqTyTrans ; [ eassumption | try assumption .. ].
        apply @TyUni ; assumption.
      }
      destruct (TermIdInversion G A u v A0 X l eq) as [[[[? ?] ?] ?] ?].
      repeat split ; try assumption.
      ceapply TermTyConv ; [ eassumption | assumption .. ].
    }

  - { assert (eq : eqtype G0 U (Uni l)).
      { ceapply EqTyCtxConv ; [ eassumption | try assumption .. ].
        - ceapply CtxSym ; assumption.
        - ceapply TyCtxConv ; [ eassumption | assumption .. ].
        - apply @TyUni ; assumption.
      }
      destruct (TermIdInversion G0 A u v U X l eq) as [[[[? ?] ?] ?] ?].
      assert (istype G A).
      { ceapply TyCtxConv ; [ eassumption | assumption .. ]. }
      repeat split.
      - assumption.
      - assumption.
      - ceapply TermCtxConv ; eassumption.
      - ceapply TermCtxConv ; [ eassumption | assumption .. ].
      - ceapply TermCtxConv ; [ eassumption | assumption .. ].
    }

  - { repeat split ; try assumption.
      pose (tyel := @tt.TyEl hasPrecond configReflection configSimpleProducts configProdEta configUniverses configWithProp configWithJ configEmpty configUnit configBool configId configPi Syntax). cbv in tyel.
      ceapply tyel ; eassumption.
    }

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

  - { simpl in H1. subst.
      assert (eqtype G (Uni l) (Uni l)).
      { capply EqTyRefl.
        - assumption.
        - apply @TyUni ; assumption.
      }
      pose proof (TermIdInversion (fl := X) G A u v (Uni l) X0 (l := l) X2).
      repeat split ; apply X3.
    }

Defined.

Fixpoint TermProdInversion `{ fl : config.universesFlag } G A B U
         (H : isterm G (Prod A B) U) {struct H} :
  forall {l}, eqtype G U (Uni l) ->
         { l1 : syntax.level &
           { l2 : syntax.level &
             (isctx G *
             istype G A *
             istype (ctxextend G A) B *
             isterm G A (Uni l1) *
             isterm (ctxextend G A) B (Uni l2))%type
           }
         }.
Proof.
  intros l h.
  inversion H ; doConfig.

  - { assert (eq : eqtype G A0 (Uni l)).
      { ceapply EqTyTrans ; [ eassumption | try assumption .. ].
        apply @TyUni ; assumption.
      }
      destruct (TermProdInversion G A B A0 X l eq)
        as [l1 [l2 [[[[? ?] ?] ?] ?]]].
      exists l1, l2.
      repeat split ; assumption.
    }

  - { assert (eq : eqtype G0 U (Uni l)).
      { ceapply EqTyCtxConv ; [ eassumption | try assumption .. ].
        - ceapply CtxSym ; assumption.
        - ceapply TyCtxConv ; [ eassumption | assumption .. ].
        - apply @TyUni ; assumption.
      }
      destruct (TermProdInversion G0 A B U X l eq)
        as [l1 [l2 [[[[? ?] ?] ?] ?]]].
      assert (istype G A).
      { ceapply TyCtxConv ; [ eassumption | assumption .. ]. }
      assert (eqctx (ctxextend G0 A) (ctxextend G A)).
      { ceapply @EqCtxExtend ; try assumption.
        capply EqTyRefl ; assumption.
      }
      assert (isctx (ctxextend G0 A)).
      { capply @CtxExtend ; assumption. }
      assert (isctx (ctxextend G A)).
      { capply @CtxExtend ; assumption. }
      exists l1, l2.
      repeat split ; try assumption.
      - ceapply TyCtxConv ; [ eassumption | assumption .. ].
      - ceapply TermCtxConv ; [ eassumption | try assumption .. ].
        apply @TyUni ; assumption.
      - ceapply TermCtxConv ; [ eassumption | try assumption .. ].
        capply @TyUni ; assumption.
    }

  - { simpl in *. subst.
      assert (istype G A).
      { pose (tyel := @tt.TyEl hasPrecond configReflection configSimpleProducts configProdEta configUniverses configWithProp configWithJ configEmpty configUnit configBool configId configPi Syntax). cbv in tyel.
        ceapply tyel ; eassumption.
      }
      exists (syntax.uni n), (syntax.uni m).
      repeat split.
      - assumption.
      - assumption.
      - pose (tyel := @tt.TyEl hasPrecond configReflection configSimpleProducts configProdEta configUniverses configWithProp configWithJ configEmpty configUnit configBool configId configPi Syntax). cbv in tyel.
        ceapply tyel ; try eassumption.
        capply @CtxExtend ; assumption.
      - assumption.
      - assumption.
    }

  - { simpl in *. subst.
      assert (istype G A).
      { pose (tyel := @tt.TyEl hasPrecond configReflection configSimpleProducts configProdEta configUniverses configWithProp configWithJ configEmpty configUnit configBool configId configPi Syntax). cbv in tyel.
        ceapply tyel ; eassumption.
      }
      exists l0, (syntax.prop).
      repeat split.
      - assumption.
      - assumption.
      - pose (tyel := @tt.TyEl hasPrecond configReflection configSimpleProducts configProdEta configUniverses configWithProp configWithJ configEmpty configUnit configBool configId configPi Syntax). cbv in tyel.
        ceapply tyel ; try eassumption.
        capply @CtxExtend ; assumption.
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

  - { simpl in *. subst.
      assert (eqtype G (Uni l) (Uni l)).
      { capply EqTyRefl.
        - assumption.
        - apply @TyUni ; assumption.
      }
      destruct (TermProdInversion (fl := X) G A B (Uni l) X0 (l := l) X2)
        as [l1 [l2 ?]].
      repeat split ; apply p.
    }

Defined.

Fixpoint TermSimProdInversion `{ fl : config.universesFlag } G A B U
         (H : isterm G (SimProd A B) U) {struct H} :
  forall {l}, eqtype G U (Uni l) ->
         { l1 : syntax.level &
           { l2 : syntax.level &
             (isctx G *
             istype G A *
             istype G B *
             isterm G A (Uni l1) *
             isterm G B (Uni l2))%type
           }
         }.
Proof.
  intros l h.
  inversion H ; doConfig.

  - { assert (eq : eqtype G A0 (Uni l)).
      { ceapply EqTyTrans ; [ eassumption | try assumption .. ].
        apply @TyUni ; assumption.
      }
      destruct (TermSimProdInversion G A B A0 X l eq)
        as [l1 [l2 [[[[? ?] ?] ?] ?]]].
      exists l1, l2.
      repeat split ; assumption.
    }

  - { assert (eq : eqtype G0 U (Uni l)).
      { ceapply EqTyCtxConv ; [ eassumption | try assumption .. ].
        - ceapply CtxSym ; assumption.
        - ceapply TyCtxConv ; [ eassumption | assumption .. ].
        - apply @TyUni ; assumption.
      }
      destruct (TermSimProdInversion G0 A B U X l eq)
        as [l1 [l2 [[[[? ?] ?] ?] ?]]].
      assert (istype G A).
      { ceapply TyCtxConv ; [ eassumption | assumption .. ]. }
      assert (eqctx (ctxextend G0 A) (ctxextend G A)).
      { ceapply @EqCtxExtend ; try assumption.
        capply EqTyRefl ; assumption.
      }
      assert (isctx (ctxextend G0 A)).
      { capply @CtxExtend ; assumption. }
      assert (isctx (ctxextend G A)).
      { capply @CtxExtend ; assumption. }
      exists l1, l2.
      repeat split ; try assumption.
      - ceapply TyCtxConv ; [ eassumption | assumption .. ].
      - ceapply TermCtxConv ; [ eassumption | try assumption .. ].
        apply @TyUni ; assumption.
      - ceapply TermCtxConv ; [ eassumption | try assumption .. ].
        capply @TyUni ; assumption.
    }

  - { simpl in *. subst.
      assert (istype G A).
      { pose (tyel := @tt.TyEl hasPrecond configReflection configSimpleProducts configProdEta configUniverses configWithProp configWithJ configEmpty configUnit configBool configId configPi Syntax). cbv in tyel.
        ceapply tyel ; eassumption.
      }
      exists (syntax.uni n), (syntax.uni m).
      repeat split.
      - assumption.
      - assumption.
      - pose (tyel := @tt.TyEl hasPrecond configReflection configSimpleProducts configProdEta configUniverses configWithProp configWithJ configEmpty configUnit configBool configId configPi Syntax). cbv in tyel.
        ceapply tyel ; eassumption.
      - assumption.
      - assumption.
    }

  - { simpl in *. subst.
      assert (istype G A).
      { pose (tyel := @tt.TyEl hasPrecond configReflection configSimpleProducts configProdEta configUniverses configWithProp configWithJ configEmpty configUnit configBool configId configPi Syntax). cbv in tyel.
        ceapply tyel ; eassumption.
      }
      exists syntax.prop, (syntax.prop).
      repeat split.
      - assumption.
      - assumption.
      - pose (tyel := @tt.TyEl hasPrecond configReflection configSimpleProducts configProdEta configUniverses configWithProp configWithJ configEmpty configUnit configBool configId configPi Syntax). cbv in tyel.
        ceapply tyel ; try eassumption.
      - assumption.
      - assumption.
    }

Defined.

Fixpoint TySimProdInversion G A B (H : istype G (SimProd A B)) {struct H} :
  isctx G * istype G A * istype G B.
Proof.
  inversion H ; doConfig.

  - { split ; [ split | .. ].
      - assumption.
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TySimProdInversion G0 A B).
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TySimProdInversion G0 A B).
    }

  - { split ; [ split | .. ] ; assumption. }

  - { simpl in *. subst.
      assert (eqtype G (Uni l) (Uni l)).
      { capply EqTyRefl.
        - assumption.
        - apply @TyUni ; assumption.
      }
      destruct (TermSimProdInversion (fl := X) G A B (Uni l) X0 (l := l) X2)
        as [l1 [l2 ?]].
      repeat split ; apply p.
    }
Defined.

Local Instance LocSyntax : syntax.Syntax := Syntax.

Local Instance haveCtxExtendInversion : inversion.HaveCtxExtendInversion
  := {| inversion.CtxExtendInversion := CtxExtendInversion |}.

Local Instance haveTyIdInversion : inversion.HaveTyIdInversion
  := {| inversion.TyIdInversion := TyIdInversion |}.

Local Instance haveTyProdInversion : inversion.HaveTyProdInversion
  := {| inversion.TyProdInversion := TyProdInversion |}.

Local Instance haveTySimProdInversion : inversion.HaveTySimProdInversion
  := {| inversion.TySimProdInversion := TySimProdInversion |}.

End ConciseSyntaxInversion.

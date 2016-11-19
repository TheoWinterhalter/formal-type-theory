Require Import reflections.

Fixpoint sane_issubst {G D sbs} :
       issubst sbs G D -> isctx G * isctx D

with sane_istype {G A} :
       istype G A -> isctx G

with sane_isterm {G A u} :
       isterm G u A -> isctx G * istype G A

with sane_eqctx {G D} :
       eqctx G D -> isctx G * isctx D

with sane_eqtype {G A B} :
       eqtype G A B -> isctx G * istype G A * istype G B

with sane_eqterm {G u v A} :
       eqterm G u v A -> isctx G * istype G A * isterm G u A * isterm G v A.

Proof.
  (****** sane_issubst ******)
  - intro H; destruct H ; split.

    (* SubstZero *)
    + now eapply (fst (sane_isterm _ _ _ _)).
    + apply CtxExtend.
      now apply (sane_isterm G A u).
    
    (* SubstWeak *)
    + now apply CtxExtend.
    + now apply (sane_istype G A).

    (* SubstShift *)
    + apply CtxExtend.
      now apply @TySubst with (D := D).
    + now apply CtxExtend.

  (****** sane_istype ******)
  - intro H; destruct H.

    (* TyCtxConv *)
    + eapply (snd (sane_eqctx G D _)).

    (* TySubst *)
    + now apply (sane_issubst G D sbs).

    (* TyProd *)
    + now apply (sane_istype G A).

    (* TyId *)
    + now apply (sane_istype G A).


  (****** sane_isterm ******)
  - intro H; destruct H; split.

    (* TermTyConv *)
    + now apply (sane_eqtype G A B).
    + now eapply (sane_eqtype G A B).

    (* TermCtxConv *)
    + now apply (sane_eqctx G D).
    + apply (@TyCtxConv G D A).
      * now apply (sane_isterm G A u).
      * assumption. 

    (* TermSubst *)
    + now apply (sane_issubst G D sbs).
    + apply @TySubst with (D := D).
      * assumption.
      * now apply (sane_isterm D A u).

    (* TermVarZero *)
    + now apply CtxExtend.
    + apply (@TySubst _ G).
      * now apply SubstWeak.
      * assumption.

    (* TermVarSucc *)
    + now apply CtxExtend.
    + apply (@TySubst _ G).
      * now apply SubstWeak.
      * now apply (sane_isterm G A (var k)).

    (* TermAbs *)
    + now apply (sane_istype G A).
    + apply TyProd.
      * assumption.
      * now apply (sane_isterm _ B u).

    (* TermApp *)
    + now apply (sane_isterm G (Prod A B) u).
    + apply @TySubst with (D := ctxextend G A).
      * now apply SubstZero.
      * assumption.

    (* TermRefl *)
    + now apply (sane_isterm G A u).
    + apply TyId.
      * now apply (sane_isterm G A u).
      * assumption.
      * assumption.

  (****** sane_eqctx ******)
  - intro H; destruct H; split.

    (* EqCtxEmpty *)
    + exact CtxEmpty.
    + exact CtxEmpty.

    (* EqCtxExtend *)
    + apply CtxExtend.
      now apply (sane_eqtype G A B).
    + apply CtxExtend.
      now apply (sane_eqtype G A B).


  (****** sane_eqtype ******)
  - intro H; destruct H; (split ; [split | idtac]).

    (* EqTyCtxConv *)
    + now apply (sane_eqctx G D).
    + apply @TyCtxConv with (G := G).
      * now apply (sane_eqtype G A B).
      * assumption.
    + apply @TyCtxConv with (G := G).
      * now apply (sane_eqtype G A B).
      * assumption.

    (* EqTyRefl: forall {G A}*)
    + now apply (sane_istype G A).
    + assumption.
    + assumption.

    (* EqTySym *)
    + now apply (sane_eqtype G A B).
    + now apply (sane_eqtype G A B).
    + now apply (sane_eqtype G A B).

    (* EqTyTrans *)
    + now apply (sane_eqtype G A B).
    + now apply (sane_eqtype G A B).
    + now apply (sane_eqtype G B C).

    (* EqTyWeakNat *)
    + apply CtxExtend.
      now apply @TySubst with (D := D).
    + eapply TySubst.
      * eapply SubstShift; eassumption.
      * eapply TySubst.
        { eapply SubstWeak; eassumption. }
        { assumption. }
    + eapply TySubst.
      * eapply SubstWeak.
        now apply @TySubst with (D := D).
      * now apply @TySubst with (D := D).

    (* EqTyWeakZero *)
    + now apply (sane_istype G A).
    + eapply TySubst.
      * now eapply SubstZero.
      * eapply TySubst.
        { apply SubstWeak. now apply (sane_isterm G B u). }
        { assumption. }
    + assumption.

    (* EqTyShiftZero *)
    + now apply (sane_issubst G D sbs).
    + eapply TySubst.
      * apply SubstZero.
        now apply @TermSubst with (D := D).
      * eapply TySubst.
        { eapply SubstShift.
          - eassumption.
          - now apply (sane_isterm D A v).
        }
        { assumption. }
    + eapply TySubst.
      * eassumption.
      * eapply TySubst.
        { now apply SubstZero. }
        { assumption. }

    (* EqTyCongZero *)
    + now apply (sane_eqtype G A1 A2).
    + eapply TySubst.
      * apply SubstZero.
        now apply (sane_eqterm G u1 u2 A1).
      * assumption.
    + eapply TySubst.
      * apply SubstZero.
        apply @TermTyConv with (A := A1).
        { now apply (sane_eqterm G u1 u2 A1). }
        { assumption. }
      * eapply @TyCtxConv.
        { eassumption. }
        { now apply EqCtxExtend. }

    (* EqTySubstProd *)
    + now apply (sane_issubst G D sbs).
    + eapply TySubst.
      * eassumption.
      * now apply TyProd.
    + apply TyProd.
      * eapply TySubst.
        { eassumption. }
        { assumption. } 
      * eapply TySubst.
        { eapply SubstShift. eassumption. assumption. }
        { assumption. }

    (* EqTySubstId *)
    + now apply (sane_issubst G D sbs).
    + eapply TySubst.
      * eassumption.
      * now apply TyId.
    + apply TyId.
      * now apply @TySubst with (D := D).
      * now apply @TermSubst with (D := D).
      * now apply @TermSubst with (D := D).

    (* CongProd *)
    + now apply (sane_eqtype G A1 B1).
    + apply TyProd.
      * now apply (sane_eqtype G A1 B1).
      * now apply (sane_eqtype _ A2 B2).
    + apply TyProd.
      * now apply (sane_eqtype G A1 B1).
      * apply @TyCtxConv with (G := ctxextend G A1).
        { now apply (sane_eqtype _ A2 B2). }
        { now apply EqCtxExtend. }


    (* CongId *)
    + now apply (sane_eqtype G A B).
    + apply TyId.
      * now apply (sane_eqtype G A B).
      * now apply (sane_eqterm G u1 v1 A).
      * now apply (sane_eqterm G u2 v2 A). 
    + apply TyId.
      * now apply (sane_eqtype G A B).
      * apply @TermTyConv with (A := A).
        { now apply (sane_eqterm G u1 v1 A). }
        { assumption. }
      * apply @TermTyConv with (A := A).
        { now apply (sane_eqterm G u2 v2 A). }
        { assumption. }

    (* CongTySubst *)
    + now apply (sane_issubst G D sbs).
    + apply @TySubst with (D := D).
      * assumption.
      * now apply (sane_eqtype D A B).
    + apply @TySubst with (D := D).
      * assumption.
      * now apply (sane_eqtype D A B).

    
  (****** sane_eqterm ******)
  - intro H; destruct H ;
    (split ; [(split ; [split | idtac]) | idtac]).


    (* EqTyConv *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqCtxConv *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqRefl *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqSym *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqTrans *)
    + admit.
    + admit.
    + admit.
    + admit.


    (* EqSubstWeak *)
    + admit.
    + admit.
    + admit.
    + admit.


    (* EqSubstZeroZero *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqSubstZeroSucc *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqSubstShiftZero *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqSubstShiftSucc *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqSubstAbs *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqSubstApp *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqSubstRefl *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* EqReflection *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* ProdBeta *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* ProdEta *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* CongAbs *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* CongApp *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* ConfRefl *)
    + admit.
    + admit.
    + admit.
    + admit.

    (* CongTermSubst *)
    + admit.
    + admit.
    + admit.
    + admit.

Admitted.


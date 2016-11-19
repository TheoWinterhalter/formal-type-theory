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
  - induction 1; split.

    (* SubstZero *)
    + apply (fst (sane_isterm _ _ _ i)).
    + apply CtxExtend, (snd (sane_isterm _ _ _ i)).
    
    (* SubstWeak *)
    + now apply CtxExtend.
    + now apply (sane_istype G A).

    (* SubstShift *)
    + apply CtxExtend.
      now apply (@TySubst _ D).
    + now apply CtxExtend.

  (****** sane_istype ******)
  - induction 1.

    (* TyCtxConv *)
    + admit.

    (* TySubst *)
    + admit.

    (* TyProd *)
    + admit.

    (* TyId *)
    + admit.


  (****** sane_isterm ******)
  - induction 1 ; split.

    (* TermTyConv *)
    + admit.
    + admit.

    (* TermCtxConv *)
    + admit.
    + admit.

    (* TermSubst *)
    + admit.
    + admit.

    (* TermVarZero *)
    + admit.
    + admit.

    (* TermVarSucc *)
    + admit.
    + admit.

    (* TermAbs *)
    + admit.
    + admit.

    (* TermApp *)
    + admit.
    + admit.

    (* TermRefl *)
    + admit.
    + admit.

  (****** sane_eqctx ******)
  - induction 1 ; split.

    (* EqCtxEmpty *)
    + admit.
    + admit.

    (* EqCtxExtend *)
    + admit.
    + admit.

  (****** sane_eqtype ******)
  - induction 1; (split ; [split | idtac]).

    (* EqTyCtxConv *)
    + admit.
    + admit.
    + admit.

    (* EqTyRefl: forall {G A}*)
    + admit.
    + admit.
    + admit.

    (* EqTySym *)
    + admit.
    + admit.
    + admit.

    (* EqTyTrans *)
    + admit.
    + admit.
    + admit.

    (* EqTyWeakNat *)
    + admit.
    + admit.
    + admit.

    (* EqTyWeakZero *)
    + admit.
    + admit.
    + admit.

    (* EqTyShiftZero *)
    + admit.
    + admit.
    + admit.

    (* EqTyCongZero *)
    + admit.
    + admit.
    + admit.

    (* EqTySubstProd *)
    + admit.
    + admit.
    + admit.

    (* EqTySubstId *)
    + admit.
    + admit.
    + admit.

    (* CongProd *)
    + admit.
    + admit.
    + admit.

    (* CongId *)
    + admit.
    + admit.
    + admit.

    (* CongTySubst *)
    + admit.
    + admit.
    + admit.
    
  (****** sane_eqterm ******)
  - induction 1 ; (split ; [(split ; [split | idtac]) | idtac]).


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


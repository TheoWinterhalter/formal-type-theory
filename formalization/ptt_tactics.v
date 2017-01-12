(* Tactics and auxiliary lemmas for ptt. *)
Require Import syntax ptt myptt.

(* Some tactic to compose substitutions. *)
Lemma eqtype_subst_left :
  forall {G D E A B sbs sbt},
    issubst sbs G D ->
    issubst sbt D E ->
    istype E A ->
    eqtype G (Subst A (sbcomp sbt sbs)) B ->
    istype G B ->
    isctx G ->
    isctx D ->
    isctx E ->
    istype G (Subst (Subst A sbt) sbs) ->
    istype G (Subst A (sbcomp sbt sbs)) ->
    eqtype G (Subst (Subst A sbt) sbs) B.
Proof.
  intros.
  eapply myEqTyTrans ; [
    eapply myEqTySubstComp ; eassumption
  | assumption ..
  ].
Defined.

Lemma eqterm_subst_left :
  forall {G D E A u v sbs sbt},
    issubst sbs G D ->
    issubst sbt D E ->
    istype E A ->
    isterm E u A ->
    eqterm G (subst u (sbcomp sbt sbs)) v (Subst A (sbcomp sbt sbs)) ->
    isctx G ->
    isctx D ->
    isctx E ->
    istype G (Subst (Subst A sbt) sbs) ->
    istype G (Subst A (sbcomp sbt sbs)) ->
    isterm G (subst (subst u sbt) sbs) (Subst A (sbcomp sbt sbs)) ->
    isterm G (subst u (sbcomp sbt sbs)) (Subst A (sbcomp sbt sbs)) ->
    isterm G v (Subst A (sbcomp sbt sbs)) ->
    eqterm G (subst (subst u sbt) sbs) v (Subst (Subst A sbt) sbs).
Proof.
  intros.
  assert (hh : eqtype G (Subst A (sbcomp sbt sbs)) (Subst (Subst A sbt) sbs)).
  { apply EqTySym ; [
      assumption ..
    | eapply myEqTySubstComp ; eassumption
    ].
  }
  assert (h : eqterm G (subst u (sbcomp sbt sbs)) v (Subst (Subst A sbt) sbs)).
  { eapply myEqTyConv ; eassumption. }
  eapply myEqTrans.
  - eapply myEqTyConv.
    + eapply myEqSubstComp ; eassumption.
    + apply EqTySym ; [
        assumption ..
      | eapply myEqTySubstComp ; eassumption
      ].
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
  - assumption.
  - assumption.
  - assumption.
  - eapply myTermTyConv ; eassumption.
  - eapply myTermTyConv ; eassumption.
  - eapply myTermTyConv ; eassumption.
Defined.

Ltac compsubst1 :=
  match goal with
  | |- eqtype ?G (Subst (Subst ?A ?sbt) ?sbs) ?B =>
    eapply eqtype_subst_left
  | |- eqtype ?G ?A (Subst (Subst ?B ?sbt) ?sbs) =>
    eapply EqTySym ; try eapply eqtype_subst_left
  | |- eqterm ?G (subst (subst ?u ?sbt) ?sbs) ?v (Subst (Subst ?A ?sbt) ?sbs) =>
    eapply eqterm_subst_left
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) (Subst (Subst ?A ?sbt) ?sbs) =>
    eapply EqSym ; try eapply eqterm_subst_left
  | |- eqterm ?G (subst (subst ?u ?sbt) ?sbs) ?v ?A =>
    eapply myEqTyConv ; [
      try eapply eqterm_subst_left
    | idtac ..
    ]
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) ?A =>
    eapply EqSym ; [
      idtac ..
    | eapply myEqTyConv ; [
        try eapply eqterm_subst_left
      | idtac ..
      ]
    ]
  | _ => fail
  end.


(* Some tactic to push substitutions inside one step. *)
(* Partial for now. *)
Ltac pushsubst1 :=
  match goal with
  | |- eqtype ?G (Subst (Subst ?A ?sbs) ?sbt) ?B =>
    eapply myEqTyTrans ; [
      eapply myCongTySubst ; [
        eapply SubstRefl
      | pushsubst1
      | idtac ..
      ]
    | idtac ..
    ]
  | |- eqtype ?G (Subst (Id ?A ?u ?v) ?sbs) ?B =>
    eapply myEqTyTrans ; [
      eapply myEqTySubstId
    | idtac ..
    ]
  | |- eqtype ?G ?A (Subst (Id ?B ?u ?v) ?sbs) =>
    eapply EqTySym ; [
      idtac ..
    | eapply myEqTyTrans ; [
        eapply myEqTySubstId
      | idtac ..
      ]
    ]
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    eapply myEqTrans ; [
      eapply myEqSubstRefl
    | idtac ..
    ]
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    eapply myEqTyConv ; [
      eapply myEqTrans ; [
        eapply myEqSubstRefl
      | idtac ..
      ]
    | idtac ..
    ]
  | _ => fail
  end.

(* Magic Tactic *)
Ltac magicn n :=
  match goal with
  | |- issubst (sbzero ?G ?A ?u) ?G1 ?G2 =>
    eapply SubstZero ; magicn n
  | |- issubst (sbweak ?G ?A) ?G1 ?G2 =>
    eapply SubstWeak ; magicn n
  | |- issubst (sbshift ?G ?A ?sbs) ?G1 ?G2 =>
    eapply mySubstShift ; magicn n
  | |- issubst (sbid ?G) ?G1 ?G2 =>
    eapply SubstId ; magicn n
  | |- issubst (sbcomp ?sbt ?sbs) ?G1 ?G2 =>
    eapply mySubstComp ; magicn n
  | |- issubst ?sbs ?G1 ?G2 =>
    eassumption
  (* We also deal with cases where we have substitutions on types or terms *)
  | |- istype ?G (Subst ?A ?sbs) =>
    eapply myTySubst ; magicn n
  | |- isterm ?G (subst ?u ?sbs) (Subst ?A ?sbs) =>
    eapply myTermSubst ; magicn n
  | |- isterm (ctxextend ?G ?A) (var 0) (Subst ?A (sbweak ?G ?A)) =>
    apply TermVarZero ; magicn n
  (* For equality of contexts we don't want to use symmetry. *)
  | |- eqctx ctxempty ctxempty =>
    now apply EqCtxEmpty
  | |- eqctx (ctxextend ?G ?A) (ctxextend ?D ?B) =>
    apply EqCtxExtend ; magicn n
  (* Equality of substitutions *)
  | |- eqsubst (sbzero ?G1 ?A1 ?u1) (sbzero ?G2 ?A2 ?u2) ?D ?E =>
    eapply myCongSubstZero ; magicn n
  (* When we want to type a context we don't want to use any of them. *)
  | |- isctx (ctxextend ?G ?A) =>
    apply CtxExtend ; magicn n
  | |- isctx ?G =>
    (* And not eassumption so we don't select some random context. *)
    assumption || shelve
  (* When all else fails. *)
  | _ =>
    match eval compute in n with
    | 0 => assumption
    | S ?n => assumption || (constructor ; magicn n)
    end
  end.

Ltac magic2 := magicn (S (S 0)).
Ltac magic3 := magicn (S (S (S 0))).
Ltac magic4 := magicn (S (S (S (S 0)))).
Ltac magic5 := magicn (S (S (S (S (S 0))))).
Ltac magic := magic2. (* ; Unshelve ; magic2. *)

(* With it we improve compsubst1 *)
Ltac gocompsubst := compsubst1 ; try magic.

(* With it we improve pushsubst1 *)
Ltac gopushsubst := pushsubst1 ; try magic.

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
    isterm E u A ->
    istype E A ->
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
(* It is basically a type checker that doesn't do the smart things,
   namely type and context conversions (and it doesn't rely on reflection
   obviously). *)
Ltac magicn n :=
  (* If we use the lazy version, we need to account for symmetries.
     We may be able to only deal with symmetries whenever we would like to
     check the different assumptions. *)
  (* It would also be very nice if we could avoid using shelve... *)
  lazymatch goal with
  (* Contexts *)
  | |- isctx ctxempty =>
    apply CtxEmpty
  | |- isctx (ctxextend ?G ?A) =>
    apply CtxExtend ; magicn n
  | |- isctx ?G =>
    (* And not eassumption so we don't select some random context. *)
    assumption || shelve
  (* Substitutions *)
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
    (* Dangerous I would like to do it only when sbs is a variable. *)
    eassumption
  (* Types *)
  | |- istype ?G (Subst ?A ?sbs) =>
    eapply myTySubst ; magicn n
  | |- istype ?G (Prod ?A ?B) =>
    eapply TyProd ; magicn n
  | |- istype ?G (Id ?A ?u ?v) =>
    eapply TyId ; magicn n
  | |- istype ?G Empty =>
    eapply TyEmpty ; magicn n
  | |- istype ?G Unit =>
    eapply TyUnit ; magicn n
  | |- istype ?G Bool =>
    eapply TyBool ; magicn n
  | |- istype ?G ?A =>
    assumption || shelve
  (* Terms *)
  | |- isterm ?G (subst ?u ?sbs) (Subst ?A ?sbs) =>
    eapply myTermSubst ; magicn n
  | |- isterm (ctxextend ?G ?A) (var 0) (Subst ?A (sbweak ?G ?A)) =>
    apply TermVarZero ; magicn n
  | |- isterm (ctxextend ?G ?B) (var (S ?k)) (Subst ?A (sbweak ?G ?B)) =>
    apply TermVarSucc ; magicn n
  (* To be continued... *)
  (* Equality of contexts *)
  | |- eqctx ctxempty ctxempty =>
    apply EqCtxEmpty
  | |- eqctx (ctxextend ?G ?A) (ctxextend ?D ?B) =>
    first [
      apply EqCtxExtend ; magicn n
    | apply myCtxSym ; [ apply EqCtxExtend ; magicn n | magicn n .. ]
    ]
  | |- eqctx ?G ?G =>
    apply CtxRefl ; magicn n
  | |- eqctx ?G ?D =>
    (* When comparing two contexts that are unknown, we either know
       already, or we know the symmetry. *)
    (* assumption *)
    (* In the first case we don't want to use magic in order to avoid symmetry
       again. *)
    (* || apply myCtxSym ; [ assumption | magicn n .. ] *)
    first [ assumption | apply myCtxSym ; [ assumption | magicn n .. ] ]
  (* Equality of substitutions *)
  | |- eqsubst (sbzero ?G1 ?A1 ?u1) (sbzero ?G2 ?A2 ?u2) ?D ?E =>
    eapply myCongSubstZero ; magicn n
  | |- eqsubst (sbweak ?G1 ?A1) (sbweak ?G2 ?A2) ?D ?E =>
    eapply myCongSubstWeak ; magicn n
  | |- eqsubst (sbshift ?G1 ?A1 ?sbs1) (sbshift ?G2 ?A2 ?sbs2) ?D ?E =>
    eapply myCongSubstShift ; magicn n
  (* We should probably avoid using congruence on composition. *)
  (* To be continued... *)
  (* Equality of types *)
  | |- eqtype ?G (Subst ?A (sbid ?G)) ?B =>
    apply EqTyIdSubst ; magicn n
  (* EqTySubst* ? *)
  | |- eqtype ?G (Subst ?A ?sbs) (Subst ?B ?sbt) =>
    eapply myCongTySubst ; magicn n
  (* To be continued... *)
  (* Equality of terms to do *)
  (* When all else fails. *)
  (* This part will hopefully be gone at some point. *)
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

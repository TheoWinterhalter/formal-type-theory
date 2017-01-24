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
  eapply EqTyTrans ; [
    eapply EqTySubstComp ; eassumption
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
    | eapply EqTySubstComp ; eassumption
    ].
  }
  assert (h : eqterm G (subst u (sbcomp sbt sbs)) v (Subst (Subst A sbt) sbs)).
  { eapply EqTyConv ; eassumption. }
  eapply EqTrans.
  - eapply EqTyConv.
    + eapply EqSubstComp ; eassumption.
    + apply EqTySym ; [
        assumption ..
      | eapply EqTySubstComp ; eassumption
      ].
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + assumption.
  - assumption.
  - assumption.
  - assumption.
  - eapply TermTyConv ; eassumption.
  - eapply TermTyConv ; eassumption.
  - eapply TermTyConv ; eassumption.
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
    eapply EqTyConv ; [
      try eapply eqterm_subst_left
    | idtac ..
    ]
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) ?A =>
    eapply EqSym ; [
      idtac ..
    | eapply EqTyConv ; [
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
    eapply EqTyTrans ; [
      eapply CongTySubst ; [
        eapply SubstRefl
      | pushsubst1
      | idtac ..
      ]
    | idtac ..
    ]
  | |- eqtype ?G (Subst (Id ?A ?u ?v) ?sbs) ?B =>
    eapply EqTyTrans ; [
      eapply EqTySubstId
    | idtac ..
    ]
  | |- eqtype ?G ?A (Subst (Id ?B ?u ?v) ?sbs) =>
    eapply EqTySym ; [
      idtac ..
    | eapply EqTyTrans ; [
        eapply EqTySubstId
      | idtac ..
      ]
    ]
  | |- eqtype ?G (Subst (Prod ?A ?B) ?sbs) ?C =>
    eapply EqTyTrans ; [
      eapply EqTySubstProd
    | idtac ..
    ]
  | |- eqtype ?G ?A (Subst (Prod ?B ?C) ?sbs) =>
    eapply EqTySym ; [
      idtac ..
    | eapply EqTyTrans ; [
        eapply EqTySubstProd
      | idtac ..
      ]
    ]
  | |- eqtype ?G (Subst Empty ?sbs) ?A =>
    eapply EqTyTrans ; [
      eapply EqTySubstEmpty
    | idtac ..
    ]
  | |- eqtype ?G ?A (Subst Empty ?sbs) =>
    eapply EqTySym ; [
      idtac ..
    | eapply EqTyTrans ; [
        eapply EqTySubstEmpty
      | idtac ..
      ]
    ]
  | |- eqtype ?G (Subst Unit ?sbs) ?A =>
    eapply EqTyTrans ; [
      eapply EqTySubstUnit
    | idtac ..
    ]
  | |- eqtype ?G ?A (Subst Unit ?sbs) =>
    eapply EqTySym ; [
      idtac ..
    | eapply EqTyTrans ; [
        eapply EqTySubstUnit
      | idtac ..
      ]
    ]
  | |- eqtype ?G (Subst Bool ?sbs) ?A =>
    eapply EqTyTrans ; [
      eapply EqTySubstBool
    | idtac ..
    ]
  | |- eqtype ?G ?A (Subst Bool ?sbs) =>
    eapply EqTySym ; [
      idtac ..
    | eapply EqTyTrans ; [
        eapply EqTySubstBool
      | idtac ..
      ]
    ]
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    eapply EqTrans ; [
      eapply EqSubstRefl
    | idtac ..
    ]
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    eapply EqTyConv ; [
      eapply EqTrans ; [
        eapply EqSubstRefl
      | idtac ..
      ]
    | idtac ..
    ]
  | |- eqterm ?G (subst true ?sbs) ?u ?A =>
    eapply EqTrans ; [
      eapply EqSubstTrue
    | idtac ..
    ]
  | |- eqterm ?G (subst true ?sbs) ?u ?A =>
    eapply EqTyConv ; [
      eapply EqTrans ; [
        eapply EqSubstTrue
      | idtac ..
      ]
    | idtac ..
    ]
  | |- eqterm ?G (subst false ?sbs) ?u ?A =>
    eapply EqTrans ; [
      eapply EqSubstFalse
    | idtac ..
    ]
  | |- eqterm ?G (subst false ?sbs) ?u ?A =>
    eapply EqTyConv ; [
      eapply EqTrans ; [
        eapply EqSubstFalse
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
  first [
    assumption
  | (* It would also be very nice if we could avoid using shelve...
       In the meantime, we should provide a tactic that doesn't shelve
       (in order to make sure we don't shelve stuff when solving the shelf). *)
    lazymatch goal with
    (*! Contexts !*)
    | |- isctx ctxempty =>
      apply CtxEmpty
    | |- isctx (ctxextend ?G ?A) =>
      eapply CtxExtend ; magicn n
    | |- isctx ?G =>
      (* And not eassumption so we don't select some random context. *)
      assumption || shelve
    (*! Substitutions !*)
    | |- issubst (sbzero ?u) ?G1 ?G2 =>
      first [
          eapply SubstZero ; magicn n
        | eassumption
        ]
    | |- issubst sbweak ?G1 ?G2 =>
      first [
          eapply SubstWeak ; magicn n
        | assumption
        | shelve
        ]
    | |- issubst (sbshift ?sbs) ?G1 ?G2 =>
      first [
          eapply SubstShift ; magicn n
        | eassumption
        ]
    | |- issubst (sbid) ?G1 ?G2 =>
      first [
          eapply SubstId ; magicn n
        | eassumption
        ]
    | |- issubst (sbcomp ?sbt ?sbs) ?G1 ?G2 =>
      first [
          eapply SubstComp ; magicn n
        | eassumption
        ]
    | |- issubst ?sbs ?G1 ?G2 =>
      (* Dangerous I would like to do it only when sbs is a variable. *)
      eassumption
    (*! Types !*)
    | |- istype ?G (Subst ?A ?sbs) =>
      eapply TySubst ; magicn n
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
    (*! Terms !*)
    | |- isterm ?G (subst ?u ?sbs) ?A =>
      eapply TermSubst ; magicn n
    | |- isterm (ctxextend ?G ?A) (var 0) ?T =>
      eapply TermVarZero ; magicn n
    | |- isterm (ctxextend ?G ?B) (var (S ?k)) (Subst ?A sbweak) =>
      eapply TermVarSucc ; magicn n
    | |- isterm ?G (lam ?A ?B ?u) ?C =>
      eapply TermAbs ; magicn n
    | |- isterm ?G (app ?u ?A ?B ?v) ?C =>
      eapply TermApp ; magicn n
    | |- isterm ?G (refl ?A ?u) ?B =>
      eapply TermRefl ; magicn n
    | |- isterm ?G (j ?A ?u ?C ?w ?v ?p) ?T =>
      eapply TermJ ; magicn n
    | |- isterm ?G (exfalso ?A ?u) _ =>
      eapply TermExfalso ; magicn n
    | |- isterm ?G unit ?A =>
      first [
          eapply TermUnit ; magicn n
        | eapply TermTyConv ; [
            eapply TermUnit ; magicn n
          | magicn n
          ]
        ]
    | |- isterm ?G true ?A =>
      first [
          eapply TermTrue ; magicn n
        | eapply TermTyConv ; [
            eapply TermTrue ; magicn n
          | magicn n
          ]
        ]
    | |- isterm ?G false ?A =>
      first [
          eapply TermFalse ; magicn n
        | eapply TermTyConv ; [
            eapply TermFalse ; magicn n
          | magicn n
          ]
        ]
    | |- isterm ?G (cond ?C ?u ?v ?w) ?T =>
      eapply TermCond ; magicn n
    | [ H : isterm ?G ?v ?A, H' : isterm ?G ?v ?B |- isterm ?G ?v ?C ] =>
      (* We have several options so we don't take any risk. *)
      first [
        is_var A ; exact H
      | is_var B ; exact H'
      | shelve
      ]
    | |- isterm ?G ?u ?A =>
      first [
        (* If u is an existential variable we don't touch it. *)
        is_evar u ; shelve
      | (* Otherwise, we can try eassumption *)
        eassumption
      ]
    (*! Equality of contexts !*)
    | |- eqctx ctxempty ctxempty =>
      apply EqCtxEmpty
    | |- eqctx (ctxextend ?G ?A) (ctxextend ?D ?B) =>
      first [
          apply EqCtxExtend ; magicn n
        | apply CtxSym ; [ apply EqCtxExtend ; magicn n | magicn n .. ]
        ]
    | |- eqctx ?G ?G =>
      apply CtxRefl ; magicn n
    | |- eqctx ?G ?D =>
      (* When comparing two contexts that are unknown, we either know
       already, or we know the symmetry. *)
      (* assumption *)
      (* In the first case we don't want to use magic in order to avoid symmetry
       again. *)
      (* || apply CtxSym ; [ assumption | magicn n .. ] *)
      first [ assumption | apply CtxSym ; [ assumption | magicn n .. ] ]
    (*! Equality of substitutions !*)
    | |- eqsubst (sbcomp sbweak (sbzero ?u)) sbid ?G ?D =>
      eapply WeakZero ; magicn n
    | |- eqsubst sbid (sbcomp sbweak (sbzero ?u)) ?G ?D =>
      eapply mySubstSym ; [
        eapply WeakZero ; magicn n
      | magicn n
      ]
    | |- eqsubst (sbzero ?u1) (sbzero ?u2) ?D ?E =>
      eapply CongSubstZero ; magicn n
    | |- eqsubst sbweak sbweak ?D ?E =>
      eapply CongSubstWeak ; magicn n
    | |- eqsubst (sbshift ?sbs1) (sbshift ?sbs2) ?D ?E =>
      eapply CongSubstShift ; magicn n
    (* We should probably avoid using congruence on composition. *)
    (* To be continued... *)
    (*! Equality of types !*)
    | |- eqtype ?G (Subst ?A (sbid)) ?B =>
      first [
        eapply EqTyIdSubst ; magicn n
      | eapply CongTySubst ; magicn n
      ]
    (* EqTySubst* ? *)
    | |- eqtype ?G (Subst ?A ?sbs) (Subst ?B ?sbt) =>
      eapply CongTySubst ; magicn n
    | |- eqtype _ (Id _ _ _) (Id _ _ _) =>
      eapply CongId ; magicn n
    (* To be continued... *)
    (*! Equality of terms !*)
    | |- eqterm ?G (subst ?u ?sbs) (subst ?v ?sbt) ?A =>
      eapply CongTermSubst ; magicn n
    (* To be continues... *)
    (* When all else fails. *)
    (* This part will hopefully be gone at some point. *)
    | _ =>
      match eval compute in n with
      | 0 => assumption
      | S ?n => assumption || (constructor ; magicn n)
      end
    end
  ].

Ltac magic2 := magicn (S (S 0)).
Ltac magic3 := magicn (S (S (S 0))).
Ltac magic4 := magicn (S (S (S (S 0)))).
Ltac magic5 := magicn (S (S (S (S (S 0))))).
Ltac magic := magic2. (* ; Unshelve ; magic2. *)

(* With it we improve compsubst1 *)
Ltac gocompsubst := compsubst1 ; try magic.

(* With it we improve pushsubst1 *)
Ltac gopushsubst := pushsubst1 ; try magic.

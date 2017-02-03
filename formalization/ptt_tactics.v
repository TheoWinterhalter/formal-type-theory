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
    eapply EqTyConv ; [ try eapply eqterm_subst_left | .. ]
  | |- eqterm ?G ?u (subst (subst ?v ?sbt) ?sbs) ?A =>
    eapply EqSym ; [
      ..
    | eapply EqTyConv ; [ try eapply eqterm_subst_left | .. ]
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
      | ..
      ]
    | ..
    ]
  | |- eqtype ?G (Subst (Id ?A ?u ?v) ?sbs) ?B =>
    eapply EqTyTrans ; [ eapply EqTySubstId | .. ]
  | |- eqtype ?G ?A (Subst (Id ?B ?u ?v) ?sbs) =>
    eapply EqTySym ; [
      ..
    | eapply EqTyTrans ; [ eapply EqTySubstId | .. ]
    ]
  | |- eqtype ?G (Subst (Prod ?A ?B) ?sbs) ?C =>
    eapply EqTyTrans ; [ eapply EqTySubstProd | .. ]
  | |- eqtype ?G ?A (Subst (Prod ?B ?C) ?sbs) =>
    eapply EqTySym ; [ .. | eapply EqTyTrans ; [ eapply EqTySubstProd | .. ] ]
  | |- eqtype ?G (Subst ?E ?sbs) Empty =>
    eapply EqTySubstEmpty
  | |- eqtype ?G (Subst Empty ?sbs) ?A =>
    eapply EqTyTrans ; [ eapply EqTySubstEmpty | .. ]
  | |- eqtype ?G Empty (Subst ?E ?sbs) =>
    eapply EqTySym ; [ eapply EqTySubstEmpty | .. ]
  | |- eqtype ?G ?A (Subst Empty ?sbs) =>
    eapply EqTySym ; [
      ..
    | eapply EqTyTrans ; [ eapply EqTySubstEmpty | .. ]
    ]
  | |- eqtype ?G (Subst Unit ?sbs) ?A =>
    eapply EqTyTrans ; [ eapply EqTySubstUnit | .. ]
  | |- eqtype ?G ?A (Subst Unit ?sbs) =>
    eapply EqTySym ; [
      ..
    | eapply EqTyTrans ; [ eapply EqTySubstUnit | .. ]
    ]
  | |- eqtype ?G (Subst Bool ?sbs) ?A =>
    eapply EqTyTrans ; [ eapply EqTySubstBool | .. ]
  | |- eqtype ?G ?A (Subst Bool ?sbs) =>
    eapply EqTySym ; [
      ..
    | eapply EqTyTrans ; [ eapply EqTySubstBool | .. ]
    ]
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    eapply EqTrans ; [ eapply EqSubstRefl | .. ]
  | |- eqterm ?G (subst (refl ?A ?u) ?sbs) ?v ?B =>
    eapply EqTyConv ; [
      eapply EqTrans ; [ eapply EqSubstRefl | .. ]
    | ..
    ]
  | |- eqterm ?G (subst true ?sbs) ?u ?A =>
    eapply EqTrans ; [ eapply EqSubstTrue | .. ]
  | |- eqterm ?G (subst true ?sbs) ?u ?A =>
    eapply EqTyConv ; [
      eapply EqTrans ; [ eapply EqSubstTrue | .. ]
    | ..
    ]
  | |- eqterm ?G (subst false ?sbs) ?u ?A =>
    eapply EqTrans ; [ eapply EqSubstFalse | .. ]
  | |- eqterm ?G (subst false ?sbs) ?u ?A =>
    eapply EqTyConv ; [
      eapply EqTrans ; [ eapply EqSubstFalse | .. ]
    | ..
    ]
  | _ => fail
  end.

Ltac cando token :=
  match token with
  | true => idtac
  | false => fail
  end.

(* Simplify tactic *)
(* Its purpose is simplifying substitutions in equalities,
   assuming the substitution is on the left. *)
Ltac simplify :=
  lazymatch goal with
  | |- eqtype ?G (Subst ?A ?sbs) ?B =>
    tryif (is_var sbs)
    then idtac
    else
      lazymatch sbs with
      | sbcomp sbweak (sbzero ?u) =>
        eapply EqTyTrans ; [
          eapply CongTySubst ; [
            eapply WeakZero
          | ..
          ]
        | ..
        ]
      | sbid =>
        eapply EqTyTrans ; [
          eapply EqTyIdSubst
        | ..
        ]
      end
  | |- eqterm ?G (subst ?u ?sbs) ?v ?A =>
    tryif (is_var sbs)
    then idtac
    else
      lazymatch sbs with
      | sbcomp sbweak (sbzero ?u) =>
        eapply EqTrans ; [
          eapply CongTermSubst ; [
            eapply WeakZero
          | ..
          ]
        | ..
        ]
      | sbid =>
        eapply EqTrans ; [
          eapply EqIdSubst
        | ..
        ]
      end
  | _ => idtac
  end.

(* Checking if we're dealing with a suitable goal. *)
(* This would be interesting in another file maybe? *)
Ltac check_goal :=
  match goal with
  | |- isctx ?G => idtac
  | |- issubst ?sbs ?G ?D => idtac
  | |- istype ?G ?A => idtac
  | |- isterm ?G ?u ?A => idtac
  | |- eqctx ?G ?D => idtac
  | |- eqsubst ?sbs ?sbt ?G ?D => idtac
  | |- eqtype ?G ?A ?B => idtac
  | |- eqterm ?G ?u ?v ?A => idtac
  | _ => fail
  end.

(* Magic Tactic *)
(* It is basically a type checker that doesn't do the smart things,
   namely type and context conversions (and it doesn't rely on reflection
   obviously). *)
Ltac magicn n try shelf tysym :=
  (* We only ever apply magic to suitable goals *)
  check_goal ;
  first [
    assumption
  | (* We have several things we need to do to the tactic:
       * Only use assumption on the base cases (not on SubstZero and the like).
       * Remove the _ case.
       * Maybe add a token that states if we can use symmetry or not.
       * Maybe add a token that states if we can shelve or not.
       * Maybe add a token that states if we should allow not to solve the goal.
       * Handle substitutions properly by pushing them in before comparing.
       * Add special rules when dealing with substitution typing this can go
         though special admissibility rules that factorize the number of
         premises that would be needed to prove.
       * Should it be able to use EqTyWeakNat?
       * Add a token to solve equalities with only one side as reflexivity.
         (Maybe shelve them in the meantime?)
       * Maybe shelve only when try token is false.
       * ... *)
    lazymatch goal with
    (*! Contexts !*)
    | |- isctx ctxempty =>
      apply CtxEmpty
    | |- isctx (ctxextend ?G ?A) =>
      eapply CtxExtend ; magicn n try shelf tysym
    | |- isctx ?G =>
      (* And not eassumption so we don't select some random context. *)
      assumption || cando shelf ; shelve
    (*! Substitutions !*)
    | |- issubst (sbzero ?u) ?G1 ?G2 =>
      first [
          eapply SubstZero ; magicn n try shelf tysym
        | eassumption
        ]
    | |- issubst sbweak ?G1 ?G2 =>
      first [
          eapply SubstWeak ; magicn n try shelf tysym
        | assumption
        | cando shelf ; shelve
        ]
    | |- issubst (sbshift ?sbs) ?G1 ?G2 =>
      first [
          eapply SubstShift ; magicn n try shelf tysym
        | eassumption
        | eapply SubstCtxConv ; magicn n try shelf tysym
        ]
    | |- issubst (sbid) ?G1 ?G2 =>
      first [
          eapply SubstId ; magicn n try shelf tysym
        | eassumption
        ]
    | |- issubst (sbcomp ?sbt ?sbs) ?G1 ?G2 =>
      first [
          eapply SubstComp ; magicn n try shelf tysym
        | eassumption
        ]
    | |- issubst ?sbs ?G1 ?G2 =>
      tryif (is_var sbs) then (
        first [
          eassumption
        | eapply SubstCtxConv ; magicn n try shelf tysym
        ]
      ) else (cando shelf ; shelve)
    (*! Types !*)
    | |- istype ?G (Subst ?A ?sbs) =>
      eapply TySubst ; magicn n try shelf tysym
    | |- istype ?G (Prod ?A ?B) =>
      eapply TyProd ; magicn n try shelf tysym
    | |- istype ?G (Id ?A ?u ?v) =>
      eapply TyId ; magicn n try shelf tysym
    | |- istype ?G Empty =>
      eapply TyEmpty ; magicn n try shelf tysym
    | |- istype ?G Unit =>
      eapply TyUnit ; magicn n try shelf tysym
    | |- istype ?G Bool =>
      eapply TyBool ; magicn n try shelf tysym
    | |- istype ?G ?A =>
      tryif (is_var A)
      then first [
        eassumption
      | eapply TyCtxConv ; [
          eassumption
        | magicn n try shelf tysym ..
        ]
      ]
      else first [
        assumption
      | cando shelf ; shelve
      ]
    (*! Terms !*)
    | |- isterm ?G (subst ?u ?sbs) ?A =>
      eapply TermSubst ; magicn n try shelf tysym
    | |- isterm (ctxextend ?G ?A) (var 0) ?T =>
      eapply TermVarZero ; magicn n try shelf tysym
    | |- isterm (ctxextend ?G ?B) (var (S ?k)) (Subst ?A sbweak) =>
      eapply TermVarSucc ; magicn n try shelf tysym
    | |- isterm ?G (lam ?A ?B ?u) ?C =>
      eapply TermAbs ; magicn n try shelf tysym
    | |- isterm ?G (app ?u ?A ?B ?v) ?C =>
      eapply TermApp ; magicn n try shelf tysym
    | |- isterm ?G (refl ?A ?u) ?B =>
      eapply TermRefl ; magicn n try shelf tysym
    | |- isterm ?G (j ?A ?u ?C ?w ?v ?p) ?T =>
      eapply TermJ ; magicn n try shelf tysym
    | |- isterm ?G (exfalso ?A ?u) _ =>
      eapply TermExfalso ; magicn n try shelf tysym
    | |- isterm ?G unit ?A =>
      first [
          eapply TermUnit ; magicn n try shelf tysym
        | eapply TermTyConv ; [
            eapply TermUnit ; magicn n try shelf tysym
          | magicn n try shelf tysym
          ]
        ]
    | |- isterm ?G true ?A =>
      first [
          eapply TermTrue ; magicn n try shelf tysym
        | eapply TermTyConv ; [
            eapply TermTrue ; magicn n try shelf tysym
          | magicn n try shelf tysym
          ]
        ]
    | |- isterm ?G false ?A =>
      first [
          eapply TermFalse ; magicn n try shelf tysym
        | eapply TermTyConv ; [
            eapply TermFalse ; magicn n try shelf tysym
          | magicn n try shelf tysym
          ]
        ]
    | |- isterm ?G (cond ?C ?u ?v ?w) ?T =>
      eapply TermCond ; magicn n try shelf tysym
    | [ H : isterm ?G ?v ?A, H' : isterm ?G ?v ?B |- isterm ?G ?v ?C ] =>
      (* We have several options so we don't take any risk. *)
      (* Eventually this should go away. I don't want to do the assert thing
         anymore. *)
      first [
        is_var A ; exact H
      | is_var B ; exact H'
      | cando shelf ; shelve
      ]
    | |- isterm ?G ?u ?A =>
      first [
        (* If u is an existential variable we don't touch it. *)
        is_evar u ; cando shelf ; shelve
      | (* Otherwise, we can try eassumption *)
        first [
          is_var u ; first [
            eassumption
          | eapply TermTyConv ; [
              eassumption
            | magicn n try shelf tysym ..
            ]
          ]
        | (* If we are typing a term variable then we shelve I guess. *)
          cando shelf ; shelve
        ]
        | eassumption
      ]
    (*! Equality of contexts !*)
    | |- eqctx ctxempty ctxempty =>
      apply EqCtxEmpty
    | |- eqctx (ctxextend ?G ?A) (ctxextend ?D ?B) =>
      first [
          eapply EqCtxExtend ; magicn n try shelf tysym
        | apply CtxSym ; [
            eapply EqCtxExtend ; magicn n try shelf tysym
          | magicn n try shelf tysym ..
          ]
        ]
    | |- eqctx ?G ?G =>
      apply CtxRefl ; magicn n try shelf tysym
    | |- eqctx ?G ?D =>
      first [
        assumption
      | apply CtxSym ; [ assumption | magicn n try shelf tysym .. ]
      | cando shelf ; shelve
      ]
    (*! Equality of substitutions !*)
    | |- eqsubst (sbcomp sbweak (sbshift ?sbs)) (sbcomp ?sbs sbweak) ?G ?D =>
      eapply WeakNat ; magicn n try shelf tysym
    | |- eqsubst (sbcomp ?sbs sbweak) (sbcomp sbweak (sbshift ?sbs)) ?G ?D =>
      eapply mySubstSym ; [
        eapply WeakNat ; magicn n try shelf tysym
      | magicn n try shelf tysym ..
      ]
    | |- eqsubst (sbcomp sbweak (sbzero ?u)) sbid ?G ?D =>
      eapply WeakZero ; magicn n try shelf tysym
    | |- eqsubst sbid (sbcomp sbweak (sbzero ?u)) ?G ?D =>
      eapply mySubstSym ; [
        eapply WeakZero ; magicn n try shelf tysym
      | magicn n try shelf tysym ..
      ]
    | |- eqsubst (sbzero ?u1) (sbzero ?u2) ?D ?E =>
      eapply CongSubstZero ; magicn n try shelf tysym
    | |- eqsubst sbweak sbweak ?D ?E =>
      eapply CongSubstWeak ; magicn n try shelf tysym
    | |- eqsubst (sbshift ?sbs1) (sbshift ?sbs2) ?D ?E =>
      eapply CongSubstShift ; magicn n try shelf tysym
    | |- eqsubst ?sbs ?sbt ?G ?D =>
      tryif (is_var sbs ; is_var sbt)
      then first [
        eassumption
      | eapply mySubstSym ; [ eassumption | magicn n try shelf tysym .. ]
      | eapply EqSubstCtxConv ; [ eassumption | magicn n try shelf tysym .. ]
      | eapply mySubstSym ; [
          eapply EqSubstCtxConv ; [ eassumption | magicn n try shelf tysym .. ]
        | magicn n try shelf tysym ..
        ]
      ]
      (* Again we cheat a bit a repeat the _ case here. *)
      else (
        match eval compute in n with
        | 0 => assumption
        | S ?n => assumption || (constructor ; magicn n try shelf tysym)
        end
      )
    (* We should probably avoid using congruence on composition. *)
    (* To be continued... *)
    (*! Equality of types !*)
    | |- eqtype ?G (Subst (Subst ?A ?sbs) ?sbt) ?B =>
      compsubst1 ; magicn n try shelf tysym
    | |- eqtype ?G ?A (Subst (Subst ?B ?sbs) ?sbt) =>
      compsubst1 ; magicn n try shelf tysym
    | |- eqtype ?G (Subst ?A ?sbs) ?B =>
      (* We should push only if it makes sense. *)
      tryif (is_var A)
      then (
        tryif (is_var sbs)
        then first [
          eapply CongTySubst ; magicn n try shelf tysym
        | eassumption
        ]
        else first [
          simplify ; magicn n try shelf tysym
        | eapply CongTySubst ; magicn n try shelf tysym
        ]
      )
      else pushsubst1 ; magicn n try shelf tysym
    | |- eqtype ?G ?A (Subst ?B ?sbs) =>
      (* We know how to deal with the symmetric case. *)
      cando tysym ; eapply EqTySym ; [
        magicn n try shelf false
      | magicn n try shelf tysym ..
      ]
    | |- eqtype ?G ?A ?B =>
      (* We only want to catch the variable case, so we will copy the _ *)
      (* case here (it's a lazymatch). *)
      tryif (is_var A ; is_var B) then (
        first [
          eassumption
        | eapply EqTyRefl ; magicn n try shelf tysym
        | cando tysym ;
          eapply EqTySym ; [ eassumption | magicn n try shelf false .. ]
        ]
      ) else (
        match eval compute in n with
        | 0 => assumption
        | S ?n => assumption || (constructor ; magicn n try shelf tysym)
        end
      )
    (* To be continued... *)
    (*! Equality of terms !*)
    | |- eqterm ?G (subst (subst ?u ?sbs) ?sbt) ?v ?A =>
      compsubst1 ; magicn n try shelf tysym
    | |- eqterm ?G ?u (subst (subst ?u ?sbs) ?sbt) ?A =>
      compsubst1 ; magicn n try shelf tysym
    (* We need to rethink the line below and only apply cong when it's ok. *)
    | |- eqterm ?G (subst ?u ?sbs) (subst ?v ?sbt) ?A =>
      eapply CongTermSubst ; magicn n try shelf tysym
    (* To be continues... *)
    (* When all else fails. *)
    (* This part will hopefully be gone at some point. *)
    | _ =>
      match eval compute in n with
      | 0 => assumption
      | S ?n => assumption || (constructor ; magicn n try shelf tysym)
      end
    end
  | cando try
  ].

Ltac magic2 := magicn (S (S 0)) false true true.
Ltac magic3 := magicn (S (S (S 0))) false true true.
Ltac magic4 := magicn (S (S (S (S 0)))) false true true.
Ltac magic5 := magicn (S (S (S (S (S 0))))) false true true.
Ltac magic := magic2.
Ltac trymagic := magicn (S (S 0)) true true true.
Ltac strictmagic := magicn (S (S 0)) false false true.

(* With it we improve compsubst1 *)
Ltac gocompsubst := compsubst1 ; try magic.

(* With it we improve pushsubst1 *)
Ltac gopushsubst := pushsubst1 ; try magic.

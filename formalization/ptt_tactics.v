(* Tactics and auxiliary lemmas for ptt. *)
Require Import syntax ptt.

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
      eapply EqTySubstComp ; eassumption
    | assumption ..
    ].
  }
  assert (h : eqterm G (subst u (sbcomp sbt sbs)) v (Subst (Subst A sbt) sbs)).
  { eapply EqTyConv ; eassumption. }
  eapply EqTrans.
  - eapply EqTyConv.
    + eapply EqSubstComp ; eassumption.
    + apply EqTySym ; [
        eapply EqTySubstComp ; eassumption
      | assumption ..
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
  lazymatch goal with
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
      eapply EqTyConv ; [ try eapply eqterm_subst_left | .. ]
    | ..
    ]
  | _ => fail
  end.


Lemma EqCompZero :
  forall {G D A u sbs},
    issubst sbs G D ->
    isterm D u A ->
    istype D A ->
    isctx G ->
    isctx D ->
    eqterm G
           (subst (var 0) (sbcomp (sbzero D A u) sbs))
           (subst u sbs)
           (Subst A sbs).
Proof.
  intros.
  assert (istype G (Subst A sbs)).
  { eapply TySubst ; eassumption. }
  assert (isterm G (subst u sbs) (Subst A sbs)).
  { eapply TermSubst ; eassumption. }
  assert (issubst (sbzero D A u) D (ctxextend D A)).
  { eapply SubstZero ; eassumption. }
  assert (isctx (ctxextend D A)).
  { eapply CtxExtend ; assumption. }
  assert (issubst (sbcomp (sbzero D A u) sbs) G (ctxextend D A)).
  { eapply SubstComp ; eassumption. }
  assert (isterm (ctxextend D A) (var 0) (Subst A (sbweak D A))).
  { apply TermVarZero ; assumption. }
  assert (issubst (sbweak D A) (ctxextend D A) D).
  { eapply SubstWeak ; assumption. }
  assert (istype (ctxextend D A) (Subst A (sbweak D A))).
  { eapply TySubst ; eassumption. }
  assert (
    isterm G
           (subst (var 0) (sbcomp (sbzero D A u) sbs))
           (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A u) sbs))
  ).
  { eapply TermSubst ; eassumption. }
  assert (istype G (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A u) sbs))).
  { eapply TySubst ; eassumption. }
  assert (issubst (sbcomp (sbweak D A) (sbcomp (sbzero D A u) sbs)) G D).
  { eapply SubstComp ; eassumption. }
  assert (istype G (Subst A (sbcomp (sbweak D A) (sbcomp (sbzero D A u) sbs)))).
  { eapply TySubst ; eassumption. }
  assert (issubst (sbcomp (sbweak D A) (sbzero D A u)) D D).
  { eapply SubstComp ; eassumption. }
  assert (issubst (sbid D) D D).
  { apply SubstId. assumption. }
  assert (issubst (sbcomp (sbcomp (sbweak D A) (sbzero D A u)) sbs) G D).
  { eapply SubstComp ; eassumption. }
  assert (issubst (sbcomp (sbid D) sbs) G D).
  { eapply SubstComp ; eassumption. }
  assert (eqsubst (sbcomp (sbweak D A) (sbcomp (sbzero D A u) sbs)) sbs G D).
  { eapply SubstTrans ; [
      eapply CompAssoc
    | eapply SubstTrans ; [
        eapply CongSubstComp ; [
          eapply SubstRefl
        | eapply WeakZero
        | ..
        ]
      | eapply CompIdLeft
      | ..
      ]
    | ..
    ] ; eassumption.
  }
  assert (eqtype D A A).
  { eapply EqTyRefl ; assumption. }
  assert (
    eqtype G (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A u) sbs)) (Subst A sbs)
  ).
  { compsubst1 ; try eassumption.
    eapply CongTySubst ; eassumption.
  }
  assert (isterm G (subst (var 0) (sbcomp (sbzero D A u) sbs)) (Subst A sbs)).
  { eapply TermTyConv ; eassumption. }
  assert (istype D (Subst (Subst A (sbweak D A)) (sbzero D A u))).
  { eapply TySubst ; eassumption. }
  assert (istype D (Subst A (sbid D))).
  { eapply TySubst ; eassumption. }
  assert (eqtype D (Subst A (sbid D)) A).
  { eapply EqTyIdSubst ; eassumption. }
  assert (eqtype D A (Subst A (sbid D))).
  { eapply EqTySym ; eassumption. }
  assert (isterm D u (Subst A (sbid D))).
  { eapply TermTyConv ; eassumption. }
  assert (istype D (Subst A (sbcomp (sbweak D A) (sbzero D A u)))).
  { eapply TySubst ; eassumption. }
  assert (eqtype D (Subst (Subst A (sbweak D A)) (sbzero D A u)) A).
  { eapply EqTyTrans ; [
      compsubst1 ; [
        eassumption
      | eassumption
      | assumption
      | eapply CongTySubst ; [
          eapply WeakZero ; [
            assumption
          | exact H1
          | ..
          ]
        | eapply EqTyRefl
        | ..
        ]
      | ..
      ]
    | ..
    ] ; eassumption.
  }
  assert (isterm D (subst (var 0) (sbzero D A u)) A).
  { eapply TermTyConv ; [
      eapply TermSubst
    | ..
    ] ; eassumption.
  }
  assert (
    eqtype G (Subst A sbs) (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A u) sbs))
  ).
  { eapply EqTySym ; eassumption. }
  assert (
    isterm G
           (subst (subst (var 0) (sbzero D A u)) sbs)
           (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A u) sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst
    | ..
    ] ; eassumption.
  }
  assert (isterm G (subst (subst (var 0) (sbzero D A u)) sbs) (Subst A sbs)).
  { eapply TermSubst ; eassumption. }
  assert (eqsubst sbs sbs G D).
  { eapply SubstRefl ; assumption. }



  eapply EqTrans ; [
    eapply EqSym ; [
      eapply EqTyConv ; [ eapply EqSubstComp | .. ]
    | ..
    ] ; eassumption
  | eapply CongTermSubst ; [
      eassumption
    | eapply EqSubstZeroZero ; assumption
    | eassumption ..
    ]
  | assumption ..
  ].
Defined.



(* Some tactic to push substitutions inside one step. *)
(* Partial for now. *)
Ltac pushsubst1 :=
  lazymatch goal with
  (*! Pushing in types !*)
  (* Is this first goal ever necessary? *)
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
  | |- eqtype ?G (Subst ?A ?sbs) (Id ?B ?u ?v) =>
    eapply EqTyTrans ; [ eapply EqTySubstId | .. ]
  | |- eqtype ?G ?A (Subst (Id ?B ?u ?v) ?sbs) =>
    eapply EqTySym ; [
      eapply EqTyTrans ; [ eapply EqTySubstId | .. ]
    | ..
    ]
  | |- eqtype ?G (Id ?A ?u ?v) (Subst ?B) =>
    eapply EqTySym ; [
      eapply EqTyTrans ; [ eapply EqTySubstId | .. ]
    | ..
    ]
  | |- eqtype ?G (Subst (Prod ?A ?B) ?sbs) ?C =>
    eapply EqTyTrans ; [ eapply EqTySubstProd | .. ]
  | |- eqtype ?G ?A (Subst (Prod ?B ?C) ?sbs) =>
    eapply EqTySym ; [ eapply EqTyTrans ; [ eapply EqTySubstProd | .. ] | .. ]
  | |- eqtype ?G (Subst ?E ?sbs) Empty =>
    eapply EqTySubstEmpty
  | |- eqtype ?G (Subst Empty ?sbs) ?A =>
    eapply EqTyTrans ; [ eapply EqTySubstEmpty | .. ]
  | |- eqtype ?G Empty (Subst ?E ?sbs) =>
    eapply EqTySym ; [ eapply EqTySubstEmpty | .. ]
  | |- eqtype ?G ?A (Subst Empty ?sbs) =>
    eapply EqTySym ; [
      eapply EqTyTrans ; [ eapply EqTySubstEmpty | .. ]
    | ..
    ]
  | |- eqtype ?G (Subst Unit ?sbs) ?A =>
    eapply EqTyTrans ; [ eapply EqTySubstUnit | .. ]
  | |- eqtype ?G ?A (Subst Unit ?sbs) =>
    eapply EqTySym ; [
      eapply EqTyTrans ; [ eapply EqTySubstUnit | .. ]
    | ..
    ]
  | |- eqtype ?G (Subst ?A ?sbs) Bool =>
    eapply EqTySubstBool
  | |- eqtype ?G (Subst Bool ?sbs) ?A =>
    eapply EqTyTrans ; [ eapply EqTySubstBool | .. ]
  | |- eqtype ?G ?A (Subst Bool ?sbs) =>
    eapply EqTySym ; [
      eapply EqTyTrans ; [ eapply EqTySubstBool | .. ]
    | ..
    ]
  (* Now, we deal with a very particuliar case. *)
  (* TODO: See if we can do without. *)
  (* | |- eqtype ?G (Subst ?A (sbzero ?u)) ?B' => *)
  (*   (* tryif (is_evar A ; is_var B') *) *)
  (*   tryif (is_evar A) *)
  (*   then ( *)
  (*     eapply @EqTyTrans with (B := Subst (Subst B' sbweak) (sbzero u)) ; [ *)
  (*       eapply EqTyRefl *)
  (*     | .. *)
  (*     ] *)
  (*   ) *)
  (*   else fail *)

  (*! Pushing in terms !*)
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
  | |- eqterm ?G (subst (var 0) (sbzero ?D ?B ?u)) ?v ?A =>
    first [
      eapply EqTrans ; [ eapply EqSubstZeroZero | .. ]
    | eapply EqTrans ; [
        eapply EqTyConv ; [ eapply EqSubstZeroZero | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G ?u (subst (var 0) (sbzero ?D ?B ?v)) ?A =>
    eapply EqSym ; [ eapply EqTrans ; [ eapply EqSubstZeroZero | .. ] | .. ]
  | |- eqterm ?G (subst (var 0) (sbshift ?D ?B ?sbs)) ?v ?A =>
    eapply EqTrans ; [
      eapply EqTyConv ; [
        eapply EqSubstShiftZero
      | ..
      ]
    | ..
    ]
  | |- eqterm ?G ?u (subst (var 0) (sbshift ?D ?B ?sbs)) ?A =>
    eapply EqSym ; [
      eapply EqTrans ; [
        eapply EqTyConv ; [
          eapply EqSubstShiftZero
        | ..
        ]
      | ..
      ]
    | ..
    ]
  | |- eqterm ?G (subst (var 0) (sbcomp (sbzero _ _ ?u) ?sbt)) ?v ?A =>
    first [
      eapply EqTrans ; [
        eapply EqCompZero
      | ..
      ]
    | eapply EqTrans ; [
        eapply EqTyConv ; [ eapply EqCompZero | .. ]
      | ..
      ]
    ]
  | |- eqterm ?G (subst (var 0) (sbcomp (sbshift _ _ ?sbs) ?sbt)) ?v ?A =>
    eapply EqTrans ; [
      eapply EqTrans ; [
        eapply EqSym ; [
          eapply EqTyConv ; [ eapply EqSubstComp | .. ]
        | ..
        ]
      | eapply EqTyConv ; [
          eapply CongTermSubst ; [
            idtac
          | eapply EqSubstShiftZero
          | ..
          ]
        | ..
        ]
      | ..
      ]
    | ..
    ]
  (* Similarly, peculiar cases. *)
  (* | |- eqterm ?G (subst ?w (sbzero ?u)) ?u ?A => *)
    (* Since it would imply a choice that I don't know how to enforce,
       I have to remove this case. *)
    (* tryif (is_evar w ; is_var u) *)
    (* then first [ *)
    (*   eapply @EqTrans with (v := subst (var 0) (sbzero u)) ; [ *)
    (*     eapply EqRefl *)
    (*   | .. *)
    (*   ] *)
    (* | eapply @EqTrans with (v := subst (subst u sbweak) (sbzero u))  ; [ *)
    (*     eapply EqRefl *)
    (*   | .. *)
    (*   ] *)
    (* ] *)
    (* else *) (* fail *)
  (* | |- eqterm ?G (subst ?w (sbzero ?v')) ?u ?A => *)
  (*   tryif (is_evar w ; is_var u) *)
  (*   then ( *)
  (*     eapply @EqTrans with (v := subst (subst u sbweak) (sbzero v'))  ; [ *)
  (*       eapply EqRefl *)
  (*     | .. *)
  (*     ] *)
  (*   ) *)
  (*   else fail *)
  | _ => fail
  end.

Ltac cando token :=
  match token with
  | true => idtac
  | false => fail
  end.

(* A simplify tactic to simplify substitutions *)
Ltac ecomp lm :=
  eapply SubstTrans ; [
    eapply CompAssoc
  | eapply CongSubstComp ; [
      eapply SubstRefl
    | eapply lm
    | ..
    ]
  | ..
  ].

Ltac simplify_subst :=
  lazymatch goal with
  | |- eqsubst ?sbs ?sbt ?G ?D =>

    (* eapply SubstTrans ; [ *)

      lazymatch sbs with

      | sbcomp (sbcomp ?sbs ?sbt) ?sbr =>
        eapply SubstSym ; [
          eapply CompAssoc
        | ..
        ]

      | sbcomp (sbid _) ?sbs =>
        eapply CompIdLeft

      | sbcomp ?sbs (sbid _) =>
        eapply CompIdRight

      | sbcomp (sbweak _ _) (sbzero _ _ _) =>
        eapply WeakZero
      | sbcomp (sbweak _ _) (sbcomp (sbzero _ _ _) _) =>
        ecomp WeakZero

      | sbcomp (sbshift _ _ ?sbs) (sbzero _ _ (subst ?u ?sbs)) =>
        eapply ShiftZero
      | sbcomp (sbshift _ _ ?sbs) (sbcomp (sbzero _ _ (subst ?u ?sbs)) _) =>
        ecomp ShiftZero
      | sbcomp (sbshift _ _ ?sbs) (sbzero _ _ _) =>
        eapply SubstTrans ; [
          eapply CongSubstComp ; [
            idtac
          | eapply SubstRefl
          | ..
          ]
        | eapply ShiftZero
        | ..
        ]
      | sbcomp (sbshift _ _ ?sbs) (sbcomp (sbzero _ _ _) _) =>
        (* Too many trans? *)
        eapply SubstTrans ; [
          eapply CompAssoc
        | eapply CongSubstComp ; [
            eapply SubstRefl
          | eapply SubstTrans ; [
              eapply CongSubstComp ; [
                idtac
              | eapply SubstRefl
              | ..
              ]
            | eapply ShiftZero
            | ..
            ]
          | ..
          ]
        | ..
        ]

      | sbcomp ?sbs ?sbt =>
        eapply CongSubstComp ; [
          simplify_subst
        | eapply SubstRefl
        | ..
        ]

      end

    (* | .. *)
    (* ] *)

  | _ => fail
  end.

(* Simplify tactic *)
(* Its purpose is simplifying substitutions in equalities,
   assuming the substitution is on the left. *)
Ltac simplify :=
  lazymatch goal with
  | |- eqtype ?G (Subst ?A (sbid ?D)) ?B =>
    eapply EqTyTrans ; [
      eapply EqTyIdSubst
    | ..
    ]

  | |- eqtype ?G (Subst ?A ?sbs) ?B =>
    eapply EqTyTrans ; [
      eapply CongTySubst ; [
        simplify_subst
      | eapply EqTyRefl
      | ..
      ]
    | ..
    ]

  | |- eqterm ?G (subst ?u (sbid _)) ?v ?A =>
    eapply EqTrans ; [
      eapply EqIdSubst
    | ..
    ]

  | |- eqterm ?G (subst ?u ?sbs) ?v ?A =>
    first [
      eapply EqTrans ; [
        eapply CongTermSubst ; [
          simplify_subst
        | eapply EqRefl
        | ..
        ]
      | ..
      ]
    | eapply EqTrans ; [
        eapply EqTyConv ; [
          eapply CongTermSubst ; [
            simplify_subst
          | eapply EqRefl
          | ..
          ]
        | ..
        ]
      | ..
      ]
    ]

  | _ => fail
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
  | _ => fail "This is not a goal meant to be handled by magic."
  end.

(* My own tactic to fail with the goal information. *)
Ltac myfail debug :=
  lazymatch goal with
  | |- ?G =>
    tryif (cando debug)
    then fail 1000 "Cannot solve subgoal " G
    else fail "Cannot solve subgoal " G
  | _ => fail "This shouldn't happen!"
  end.

(* Factorizing some cases *)
Ltac eqtype_subst G A sbs B k n try shelf tysym debug :=
  tryif (is_var A)
  then (
    tryif (is_var sbs)
    then (
      match B with
      | Subst ?B ?sbt =>
        tryif (is_var B)
        then (
          tryif (is_var sbt)
          then first [
            eapply CongTySubst
          | eassumption
          | myfail debug
          ] ; k n try shelf true debug
          else first [
            eapply EqTySym ; [ simplify | .. ]
          | eapply CongTySubst
          | myfail debug
          ] ; k n try shelf true debug
        )
        else first [
          pushsubst1
        | myfail debug
        ] ; k n try shelf true debug
      | _ =>
        first [
          eapply CongTySubst
        | eassumption
        | myfail debug
        ] ; k n try shelf true debug
      end
    )
    else first [
      simplify
    | eapply CongTySubst
    | myfail debug
    ] ; k n try shelf true debug
  )
  else first [
    pushsubst1
  | cando tysym ; eapply EqTySym ; [ simplify | .. ]
  | myfail debug
  ] ; k n try shelf true debug.

Ltac falling_case magicn n try shelf true debug :=
  match eval compute in n with
  | 0 => assumption
  | S ?n => assumption || (constructor ; magicn n try shelf true debug)
  end.

(* Magic Tactic *)
(* It is basically a type checker that doesn't do the smart things,
   namely type and context conversions (and it doesn't rely on reflection
   obviously). *)
Ltac magicn n try shelf tysym debug :=
  (* We only ever apply magic to suitable goals *)
  check_goal ;
  first [
    assumption
  | (* We have several things we need to do to the tactic:
       * Only use assumption on the base cases (not on SubstZero and the like).
       * Remove the _ case.
       * Add special rules when dealing with substitution typing this can go
         though special admissibility rules that factorize the number of
         premises that would be needed to prove.
       * Should it be able to use EqTyWeakNat?
       * Add a token to solve equalities with only one side as reflexivity.
         (Maybe shelve them in the meantime?)
       * Put tysym token back to true whenever progress is made
         (ie not when using structural rules).
       * [NEW] We can take advantage of the information we have at hand on
         substitutions to make magic finer!
       * ... *)
    lazymatch goal with
    (*! Contexts !*)
    | |- isctx ctxempty =>
      apply CtxEmpty
    | |- isctx (ctxextend ?G ?A) =>
      eapply CtxExtend ; magicn n try shelf true debug
    | |- isctx ?G =>
      (* And not eassumption so we don't select some random context. *)
      first [
        assumption
      | cando shelf ; shelve
      ]

    (*! Substitutions !*)
    | |- issubst (sbzero _ _ ?u) ?G1 ?G2 =>
      first [
        eapply SubstZero
      | eassumption
      | eapply SubstCtxConv ; [ eapply SubstZero | .. ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- issubst (sbweak _ _) ?G1 ?G2 =>
      first [
        eapply SubstWeak
      | assumption
      (* | cando shelf ; shelve *) (* We probably don't need to do it anymore. *)
      | eapply SubstCtxConv ; [ eapply SubstWeak | .. ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- issubst (sbshift _ _ ?sbs) ?G1 ?G2 =>
      first [
        eapply SubstShift
      | eassumption
      | eapply SubstCtxConv ; [ eapply SubstShift | .. ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- issubst (sbid _) ?G1 ?G2 =>
      first [
        eapply SubstId
      | eassumption
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- issubst (sbcomp ?sbt ?sbs) ?G1 ?G2 =>
      first [
          eapply SubstComp
        | eassumption
        | myfail debug
        ] ; magicn n try shelf true debug
    | |- issubst ?sbs ?G1 ?G2 =>
      tryif (is_var sbs) then (
        first [
          eassumption
        | eapply SubstCtxConv
        | myfail debug
        ] ; magicn n try shelf tysym debug
      ) else (cando shelf ; shelve)

    (*! Types !*)
    | |- istype ?G (Subst ?A ?sbs) =>
      first [
        eapply TySubst
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- istype ?G (Prod ?A ?B) =>
      first [
        eapply TyProd
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- istype ?G (Id ?A ?u ?v) =>
      first [
        eapply TyId
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- istype ?G Empty =>
      first [
        eapply TyEmpty
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- istype ?G Unit =>
      first [
        eapply TyUnit
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- istype ?G Bool =>
      first [
        eapply TyBool
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- istype ?G ?A =>
      tryif (is_var A)
      then first [
        eassumption
      | eapply TyCtxConv ; [
          eassumption
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
      else first [
        assumption
      | cando shelf ; shelve
      ]

    (*! Terms !*)
    | |- isterm ?G (subst ?u ?sbs) ?A =>
      first [
        eapply TermSubst
      | eapply TermTyConv ; [
          eapply TermSubst
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm (ctxextend ?G ?A) (var 0) ?T =>
      first [
        eapply TermVarZero
      | eapply TermTyConv ; [ eapply TermVarZero | .. ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm (ctxextend ?G ?B) (var (S ?k)) ?A =>
      first [
        eapply TermVarSucc
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm ?G (lam ?A ?B ?u) ?C =>
      first [
        eapply TermAbs
      | eapply TermTyConv ; [
          eapply TermAbs
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm ?G (app ?u ?A ?B ?v) ?C =>
      first [
        eapply TermApp
      | eapply TermTyConv ; [ eapply TermApp | .. ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm ?G (refl ?A ?u) ?B =>
      first [
        eapply TermRefl
      | eapply TermTyConv ; [ eapply TermRefl | .. ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm ?G (j ?A ?u ?C ?w ?v ?p) ?T =>
      first [
        eapply TermJ
      | eapply TermTyConv ; [ eapply TermJ | .. ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm ?G (exfalso ?A ?u) _ =>
      first [
        eapply TermExfalso
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm ?G unit ?A =>
      first [
        eapply TermUnit
      | eapply TermTyConv ; [
          eapply TermUnit
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm ?G true ?A =>
      first [
        eapply TermTrue
      | eapply TermTyConv ; [
          eapply TermTrue
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm ?G false ?A =>
      first [
        eapply TermFalse
      | eapply TermTyConv ; [
          eapply TermFalse
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- isterm ?G (cond ?C ?u ?v ?w) ?T =>
      first [
        eapply TermCond
      | eapply TermTyConv ; [ eapply TermCond | .. ]
      | myfail debug
      ] ; magicn n try shelf true debug
    (* This might go away some day. *)
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
      tryif (is_evar u)
      (* If u is an existential variable we don't touch it. *)
      then (cando shelf ; shelve)
      else (
        tryif (is_var u)
        then first [
          eassumption
        | eapply TermTyConv ; [
            eassumption
          | ..
          ]
        | eapply TermCtxConv ; [
            eassumption
          | ..
          ]
        | eapply TermCtxConv ; [
            eapply TermTyConv ; [
              eassumption
            | ..
            ]
          | ..
          ]
        | myfail debug
        ] ; magicn n try shelf true debug
        else cando shelf ; shelve
      )

    (*! Equality of contexts !*)
    | |- eqctx ctxempty ctxempty =>
      apply EqCtxEmpty
    | |- eqctx (ctxextend ?G ?A) (ctxextend ?D ?B) =>
      first [
        eapply EqCtxExtend
      | apply CtxSym ; [
          eapply EqCtxExtend
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqctx ?G ?G =>
      first [
        apply CtxRefl
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqctx ?G ?D =>
      first [
        assumption
      | apply CtxSym ; [ assumption | .. ]
      | cando shelf ; shelve
      ] ; magicn n try shelf true debug

    (*! Equality of substitutions !*)
    | |- eqsubst (sbcomp (sbweak _ _) (sbshift _ _ ?sbs))
                (sbcomp ?sbs (sbweak _ _)) ?G ?D =>
      first [
        eapply WeakNat
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqsubst (sbcomp ?sbs (sbweak _ _))
                (sbcomp (sbweak _ _) (sbshift _ _ ?sbs)) ?G ?D =>
      first [
        eapply SubstSym ; [
          eapply WeakNat
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqsubst (sbcomp (sbweak _ _) (sbzero _ _ ?u)) (sbid _) ?G ?D =>
      first [
        eapply WeakZero
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqsubst (sbid _) (sbcomp (sbweak _ _) (sbzero _ ?u)) ?G ?D =>
      first [
        eapply SubstSym ; [
          eapply WeakZero
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqsubst (sbcomp (sbshift _ _ ?sbs) (sbzero _ _ (subst ?u ?sbs)))
                (sbcomp (sbzero _ _ ?u) ?sbs) ?G ?D =>
      first [
        eapply ShiftZero
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqsubst (sbcomp (sbshift ?G1 ?A1 ?sbs) (sbzero ?G2 ?A2 ?v))
                (sbcomp (sbzero _ _ ?u) ?sbs) ?G ?D =>
      first [
        eapply @SubstTrans
        with (sb2 := sbcomp (sbshift G1 A1 sbs) (sbzero G2 A2 (subst u sbs))) ; [
          eapply CongSubstComp
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqsubst (sbcomp (sbzero _ _ ?u) ?sbs)
                (sbcomp (sbshift _ _ ?sbs) (sbzero _ _ (subst ?u ?sbs))) ?G ?D =>
      first [
        eapply SubstSym ; [
          eapply ShiftZero
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqsubst (sbzero _ _ ?u1) (sbzero _ _ ?u2) ?D ?E =>
      first [
        eapply CongSubstZero
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqsubst (sbweak _ _) (sbweak _ _) ?D ?E =>
      first [
        eapply CongSubstWeak ; magicn n try shelf true debug
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqsubst (sbshift _ _ ?sbs1) (sbshift _ _ ?sbs2) ?D ?E =>
      first [
        eapply CongSubstShift
      | eapply EqSubstCtxConv ; [
          eapply CongSubstShift
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqsubst ?sbs ?sbs ?G ?D =>
      first [
          eapply SubstRefl
        | myfail debug
        ] ; magicn n try shelf true debug
    (* We need to simplify if we are ever going to apply congruence for
       composition. *)
    | |- eqsubst ?sbs ?sbt ?G ?D =>
      tryif (is_var sbs ; is_var sbt)
      then first [
        eassumption
      | eapply SubstSym ; [ eassumption | .. ]
      | eapply EqSubstCtxConv ; [ eassumption | .. ]
      | eapply SubstSym ; [
          eapply EqSubstCtxConv ; [ eassumption | .. ]
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
      else first [
        eapply SubstTrans ; [ simplify_subst | .. ]
      | eapply SubstSym ; [ eapply SubstTrans ; [ simplify_subst | .. ] | .. ]
      | eapply CongSubstComp
      | myfail debug
      ] ; magicn n try shelf true debug

    (*! Equality of types !*)
    | |- eqtype ?G (Subst (Subst ?A ?sbs) ?sbt) ?B =>
      first [
        compsubst1
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqtype ?G ?A (Subst (Subst ?B ?sbs) ?sbt) =>
      first [
        compsubst1
      | myfail debug
      ] ; magicn n try shelf true debug
    (* A weird case perhaps. *)
    (* It feels like we should improve the case where is_var A and
       not is_var sbs below. *)
    | |- eqtype ?G (Subst ?B' (sbcomp ?sbs (sbweak ?G1 (Subst ?A1 ?sbs))))
               (Subst ?A (sbshift ?G2 ?A2 ?sbs)) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := Subst B' (sbweak _ _))
        | myfail debug
        ] ; magicn n try shelf true debug
      )
      else eqtype_subst G (Subst B' (sbcomp sbs (sbweak A1 sbs)))
                        (Subst A (sbshift G2 A2 sbs))
                        magicn n try shelf tysym debug
    | |- eqtype ?G
               (Subst ?A
                      (sbcomp (sbshift ?G1 ?A1 ?sbs)
                              (sbzero ?G2 ?A2 (subst ?u ?sbs))))
               (Subst ?B' ?sbs) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := Subst B' (sbweak _ _))
        | myfail debug
        ] ; magicn n try shelf true debug
      )
      else eqtype_subst G
                        A
                        (sbcomp (sbshift G1 A1 sbs)
                                (sbzero G2 A2 (subst u sbs)))
                        (Subst B' sbs)
                        magicn n try shelf tysym debug
    | |- eqtype ?G (Subst ?B' ?sbs)
               (Subst ?A (sbcomp (sbshift ?G1 ?A1 ?sbs)
                                 (sbzero ?G2 ?A2 (subst ?u ?sbs)))) =>
      tryif (is_evar A ; is_var B')
      then (
        first [
          instantiate (1 := Subst B' (sbweak _ _))
        | myfail debug
        ] ; magicn n try shelf true debug
      )
      else eqtype_subst G B' sbs
                        (Subst A (sbcomp (sbshift G1 A1 sbs)
                                         (sbzero G2 A2 (subst u sbs))))
                        magicn n try shelf tysym debug
    (* Another case I'm not sure of. *)
    | |- eqtype ?G
               (Subst ?A ?sbs)
               (Subst ?B (sbzero ?D (Subst ?A ?sbs) (subst ?u ?sbs))) =>
      tryif (is_var A ; is_evar B)
      then
        first [
          instantiate (1 := Subst (Subst A sbs) (sbweak _ _))
        | myfail debug
        ] ; magicn n try shelf true debug
      else
        eqtype_subst G A sbs (Subst B (sbzero D (Subst A sbs) (subst u sbs)))
                     magicn n try shelf tysym debug
    (* One more *)
    | |- eqtype ?G (Subst ?A (sbzero ?D ?B ?u)) ?B =>
      tryif (is_evar A ; is_var B)
      then first [
        instantiate (1 := Subst B (sbweak _ _))
      | myfail debug
      ] ; magicn n try shelf true debug
      else eqtype_subst G A (sbzero D B u) B
                        magicn n try shelf tysym debug
    | |- eqtype ?G (Subst ?A ?sbs) ?B =>
      (* We should push only if it makes sense. *)
      eqtype_subst G A sbs B magicn n try shelf tysym debug
    | |- eqtype ?G ?A (Subst ?B ?sbs) =>
      (* We know how to deal with the symmetric case. *)
      cando tysym ; eapply EqTySym ; [
        magicn n try shelf false debug
      | magicn n try shelf true debug ..
      ]
    | |- eqtype ?G (Id ?A ?u ?v) (Id ?B ?w ?z) =>
      first [
        eapply CongId
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqtype ?G (Prod ?A ?B) (Prod ?C ?D) =>
      first [
        eapply CongProd
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqtype ?G Bool Bool =>
      first [
        eapply EqTyRefl
      | myfail debug
      ] ; magicn n try shelf true debug
    | |- eqtype ?G ?A ?B =>
      tryif (is_var A ; is_var B)
      then (
        first [
          eassumption
        | eapply EqTyRefl
        | eapply EqTySym ; [ eassumption | .. ]
        | eapply EqTyCtxConv ; [
            first [
              eassumption
            | eapply EqTySym ; [ eassumption | .. ]
            ]
          | ..
          ]
        | myfail debug
        ] ; magicn n try shelf true debug
      )
      else falling_case magicn n try shelf tysym debug

    (*! Equality of terms !*)
    | |- eqterm ?G (subst (subst ?u ?sbs) ?sbt) ?v ?A =>
      compsubst1 ; magicn n try shelf true debug
    | |- eqterm ?G ?u (subst (subst ?v ?sbs) ?sbt) ?A =>
      compsubst1 ; magicn n try shelf true debug
    | |- eqterm ?G (subst ?u ?sbs) ?v ?A =>
      (* Maybe some type conversion somewhere. *)
      tryif (is_var u)
      then (
        tryif (is_var sbs)
        then (
          match v with
          | subst ?v ?sbt =>
            tryif (is_var v)
            then (
              tryif (is_var sbt)
              then first [
                eapply CongTermSubst
              | eapply EqTyConv ; [
                  eapply CongTermSubst
                | ..
                ]
              | eassumption
              | myfail debug
              ] ; magicn n try shelf true debug
              else first [
                eapply EqSym ; [ simplify | .. ]
              | eapply CongTermSubst
              | eapply EqTyConv ; [
                  eapply CongTermSubst
                | ..
                ]
              | myfail debug
              ] ; magicn n try shelf true debug
            )
            else first [
              pushsubst1
            | eapply EqSym ; [ pushsubst1 | .. ]
            | cando shelf ; shelve
            ] ; magicn n try shelf true debug
          | _ =>
            first [
              eapply CongTermSubst
            | eapply EqTyConv ; [
              eapply CongTermSubst
              | ..
              ]
            | eassumption
            | myfail debug
            ] ; magicn n try shelf true debug
          end
        )
        else (
          lazymatch v with
          | subst ?v ?sbt =>
            tryif (is_var v)
            then first [
                simplify
              | eapply CongTermSubst
              | eapply EqTyConv ; [ eapply CongTermSubst | .. ]
              | myfail debug
              ] ; magicn n try shelf true debug
            else first [
                pushsubst1 ; magicn n try shelf true debug
              | cando shelf ; shelve
            ]

          | _ =>
            first [
              simplify
            | cando shelf ; shelve
            ] ; magicn n try shelf true debug
          end
        )
      )
      else first [
        pushsubst1 ; magicn n try shelf true debug
      | cando shelf ; shelve
      ]
    | |- eqterm ?G ?u (subst ?v ?sbs) ?A =>
      (* We know how to deal with the symmetric case. *)
      (* We use the token tysym, maybe we should have some dedicated tmsym... *)
      cando tysym ; eapply EqSym ; [
        magicn n try shelf false debug
      | magicn n try shelf true debug ..
      ]
    | |- eqterm ?G ?u ?v ?A =>
      tryif (is_var u ; is_var v)
      then first [
        eassumption
      | eapply EqRefl
      | eapply EqSym ; [
          eassumption
        |..
        ]
      | eapply EqTyConv ; [ eassumption | .. ]
      | eapply EqTyConv ; [
          eapply EqSym ; [ eassumption | .. ]
        | ..
        ]
      | myfail debug
      ] ; magicn n try shelf true debug
      else falling_case magicn n try shelf tysym debug
    (* To be continued... *)
    (* When all else fails. *)
    (* This part will hopefully be gone at some point. *)
    (* And replaced by fail probably. *)
    | _ => myfail debug
    end
  | cando try
  ].

Ltac magic2 := magicn (S (S 0)) false true true true.
Ltac magic3 := magicn (S (S (S 0))) false true true true.
Ltac magic4 := magicn (S (S (S (S 0)))) false true true true.
Ltac magic5 := magicn (S (S (S (S (S 0))))) false true true true.
Ltac magic := magic2.
Ltac okmagic := magicn (S (S 0)) false true true false.
Ltac trymagic := magicn (S (S 0)) true true true false.
Ltac strictmagic := magicn (S (S 0)) false false true true.

(* With it we improve compsubst1 *)
Ltac gocompsubst := compsubst1 ; try magic.

(* With it we improve pushsubst1 *)
Ltac gopushsubst := pushsubst1 ; try magic.

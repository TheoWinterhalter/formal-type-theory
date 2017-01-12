(* Admissibile ptt rules. *)

Require Import syntax ptt myptt ptt_tactics.

(* Some preliminary lemmata *)
Lemma EqTyWeakNat :
  forall {G D A B sbs},
    issubst sbs G D ->
    istype D A ->
    istype D B ->
    isctx G ->
    isctx D ->
    eqtype (ctxextend G (Subst A sbs))
           (Subst (Subst B (sbweak D A)) (sbshift G A sbs))
           (Subst (Subst B sbs) (sbweak G (Subst A sbs))).
Proof.
  intros. gocompsubst. gocompsubst.
  eapply myCongTySubst ; magic.
  Unshelve. assumption.
Defined.


Lemma compWeakZero :
  forall {G A B u},
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u B ->
    eqtype G A (Subst A (sbcomp (sbweak G B) (sbzero G B u))).
Proof.
  intros.
  eapply EqTySym ; try magic.
  eapply myEqTyTrans ; [
    eapply myCongTySubst ; [
      eapply WeakZero ; magic
    | magic ..
    ]
  | magic ..
  ].
Defined.

Lemma EqTyWeakZero :
  forall {G A B u},
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u B ->
    eqtype G A (Subst (Subst A (sbweak G B)) (sbzero G B u)).
Proof.
  intros.
  gocompsubst. eapply EqTySym ; try magic. apply compWeakZero ; magic.
Defined.

Lemma EqTyShiftZero :
  forall {G D A B v sbs},
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    isterm D v A ->
    isctx G ->
    isctx D ->
    eqtype
      G
      (Subst (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
      (Subst (Subst B (sbzero D A v)) sbs).
Proof.
  intros. gocompsubst. gocompsubst.
  eapply myCongTySubst ; magic.
  Unshelve. magic.
Defined.

Lemma EqTyCongZero :
  forall {G A1 A2 B1 B2 u1 u2},
    isctx G ->
    eqtype G A1 B1 ->
    eqterm G u1 u2 A1 ->
    eqtype (ctxextend G A1) A2 B2 ->
    istype (ctxextend G A1) A2 ->
    istype (ctxextend G A1) B2 ->
    eqtype G
           (Subst A2 (sbzero G A1 u1))
           (Subst B2 (sbzero G B1 u2)).
Proof.
  intros.
  eapply myCongTySubst.
  - admit. (* We need to strengthen magic. *)
  - eassumption. (* Same here... *)
  - magic.
  - magic.
  - magic.
  - magic.
  - admit. (* Weird it doesn't solve this. *)
  - admit.
Admitted.


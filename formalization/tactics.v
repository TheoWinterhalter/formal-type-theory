(* Some useful tactics. *)

Require Import syntax.
Require ett ptt.
Require ptt2ett ett2ptt.

(* Tactics to apply an hypothesis that could be in PTT instead of ETT. *)
Ltac pttassumption :=
  match goal with
  | [ H : ptt.isctx ?G |- ett.isctx ?G ] =>
    exact (ptt2ett.sane_isctx G H)
  | [ H : ptt.issubst ?sbs ?G ?D |- ett.issubst ?sbs ?G ?D ] =>
    exact (ptt2ett.sane_issubst sbs G D H)
  | [ H : ptt.istype ?G ?A |- ett.istype ?G ?A ] =>
    exact (ptt2ett.sane_istype G A H)
  | [ H : ptt.isterm ?G ?u ?A |- ett.isterm ?G ?u ?A ] =>
    exact (ptt2ett.sane_isterm G u A H)
  | [ H : ptt.eqctx ?G ?D |- ett.eqctx ?G ?D ] =>
    exact (ptt2ett.sane_eqctx G D H)
  | [ H : ptt.eqtype ?G ?A ?B |- ett.eqtype ?G ?A ?B ] =>
    exact (ptt2ett.sane_eqtype G A B H)
  | [ H : ptt.eqterm ?G ?u ?v ?A |- ett.eqterm ?G ?u ?v ?A ] =>
    exact (ptt2ett.sane_eqterm G u v A H)
  end.

Ltac hyp := first [ assumption | pttassumption ].

Ltac epttassumption :=
  match goal with
  | [ H : ptt.isctx ?G |- ett.isctx _ ] =>
    exact (ptt2ett.sane_isctx G H)
  | [ H : ptt.issubst ?sbs ?G ?D |- ett.issubst _ _ _ ] =>
    exact (ptt2ett.sane_issubst sbs G D H)
  | [ H : ptt.istype ?G ?A |- ett.istype _ _ ] =>
    exact (ptt2ett.sane_istype G A H)
  | [ H : ptt.isterm ?G ?u ?A |- ett.isterm _ _ _ ] =>
    exact (ptt2ett.sane_isterm G u A H)
  | [ H : ptt.eqctx ?G ?D |- ett.eqctx _ _ ] =>
    exact (ptt2ett.sane_eqctx G D H)
  | [ H : ptt.eqtype ?G ?A ?B |- ett.eqtype _ _ _ ] =>
    exact (ptt2ett.sane_eqtype G A B H)
  | [ H : ptt.eqterm ?G ?u ?v ?A |- ett.eqterm _ _ _ _ ] =>
    exact (ptt2ett.sane_eqterm G u v A H)
  end.

Ltac ehyp := first [ eassumption | epttassumption ].

(* A tactic to apply sanity in ptt. *)
Ltac ptt_sane :=
  match goal with
  | H : ptt.issubst ?sbs ?G ?D |- ptt.isctx ?G =>
    now apply (ptt_sanity.sane_issubst sbs G D)
  | H : ptt.issubst ?sbs ?G ?D |- ptt.isctx ?D =>
    now apply (ptt_sanity.sane_issubst sbs G D)
  | H : ptt.istype ?G ?A |- ptt.isctx ?G =>
    now apply (ptt_sanity.sane_istype G A)
  | H : ptt.isterm ?G ?u ?A |- ptt.isctx ?G =>
    now apply (ptt_sanity.sane_isterm G u A)
  | H : ptt.isterm ?G ?u ?A |- ptt.istype ?G ?A =>
    now apply (ptt_sanity.sane_isterm G u A)
  | H : ptt.eqctx ?G ?D |- ptt.isctx ?G =>
    now apply (ptt_sanity.sane_eqctx G D)
  | H : ptt.eqctx ?G ?D |- ptt.isctx ?D =>
    now apply (ptt_sanity.sane_eqctx G D)
  | H : ptt.eqsubst ?sbs ?sbt ?G ?D |- ptt.isctx ?G =>
    now apply (ptt_sanity.sane_eqsubst sbs sbt G D)
  | H : ptt.eqsubst ?sbs ?sbt ?G ?D |- ptt.isctx ?D =>
    now apply (ptt_sanity.sane_eqsubst sbs sbt G D)
  | H : ptt.eqsubst ?sbs ?sbt ?G ?D |- ptt.issubst ?sbs ?G ?D =>
    now apply (ptt_sanity.sane_eqsubst sbs sbt G D)
  | H : ptt.eqsubst ?sbs ?sbt ?G ?D |- ptt.issubst ?sbt ?G ?D =>
    now apply (ptt_sanity.sane_eqsubst sbs sbt G D)
  | H : ptt.eqtype ?G ?A ?B |- ptt.isctx ?G =>
    now apply (ptt_sanity.sane_eqtype G A B)
  | H : ptt.eqtype ?G ?A ?B |- ptt.istype ?G ?A =>
    now apply (ptt_sanity.sane_eqtype G A B)
  | H : ptt.eqtype ?G ?A ?B |- ptt.istype ?G ?B =>
    now apply (ptt_sanity.sane_eqtype G A B)
  | H : ptt.eqterm ?G ?u ?v ?A |- ptt.isctx ?G =>
    now apply (ptt_sanity.sane_eqterm G u v A)
  | H : ptt.eqterm ?G ?u ?v ?A |- ptt.istype ?G ?A =>
    now apply (ptt_sanity.sane_eqterm G u v A)
  | H : ptt.eqterm ?G ?u ?v ?A |- ptt.isterm ?G ?u ?A =>
    now apply (ptt_sanity.sane_eqterm G u v A)
  | H : ptt.eqterm ?G ?u ?v ?A |- ptt.isterm ?G ?v ?A =>
    now apply (ptt_sanity.sane_eqterm G u v A)
  end.

Ltac hyps := first [ hyp | ptt_sane ].
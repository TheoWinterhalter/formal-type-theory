(* Some useful tactics. *)

Require Import syntax.
Require ett ptt.
Require ptt2ett ett2ptt.
Require ett_sanity.

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

(* The converse. *)
Ltac ettassumption :=
  match goal with
  | [ H : ett.isctx ?G |- ptt.isctx ?G ] =>
    exact (ett2ptt.sane_isctx G H)
  | [ H : ett.issubst ?sbs ?G ?D |- ptt.issubst ?sbs ?G ?D ] =>
    exact (ett2ptt.sane_issubst sbs G D H)
  | [ H : ett.istype ?G ?A |- ptt.istype ?G ?A ] =>
    exact (ett2ptt.sane_istype G A H)
  | [ H : ett.isterm ?G ?u ?A |- ptt.isterm ?G ?u ?A ] =>
    exact (ett2ptt.sane_isterm G u A H)
  | [ H : ett.eqctx ?G ?D |- ptt.eqctx ?G ?D ] =>
    exact (ett2ptt.sane_eqctx G D H)
  | [ H : ett.eqtype ?G ?A ?B |- ptt.eqtype ?G ?A ?B ] =>
    exact (ett2ptt.sane_eqtype G A B H)
  | [ H : ett.eqterm ?G ?u ?v ?A |- ptt.eqterm ?G ?u ?v ?A ] =>
    exact (ett2ptt.sane_eqterm G u v A H)
  end.

Ltac hyp := first [ assumption | pttassumption | ettassumption ].

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

Ltac eettassumption :=
  match goal with
  | [ H : ett.isctx ?G |- ptt.isctx _ ] =>
    exact (ett2ptt.sane_isctx G H)
  | [ H : ett.issubst ?sbs ?G ?D |- ptt.issubst _ _ _ ] =>
    exact (ett2ptt.sane_issubst sbs G D H)
  | [ H : ett.istype ?G ?A |- ptt.istype _ _ ] =>
    exact (ett2ptt.sane_istype G A H)
  | [ H : ett.isterm ?G ?u ?A |- ptt.isterm _ _ _ ] =>
    exact (ett2ptt.sane_isterm G u A H)
  | [ H : ett.eqctx ?G ?D |- ptt.eqctx _ _ ] =>
    exact (ett2ptt.sane_eqctx G D H)
  | [ H : ett.eqtype ?G ?A ?B |- ptt.eqtype _ _ _ ] =>
    exact (ett2ptt.sane_eqtype G A B H)
  | [ H : ett.eqterm ?G ?u ?v ?A |- ptt.eqterm _ _ _ _ ] =>
    exact (ett2ptt.sane_eqterm G u v A H)
  end.

Ltac ehyp := first [ eassumption | epttassumption | eettassumption ].

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

(* A tactic to apply sanity in ett. *)
Ltac ett_sane :=
  match goal with
  | H : ett.issubst ?sbs ?G ?D |- ett.isctx ?G =>
    now apply (ett_sanity.sane_issubst sbs G D)
  | H : ett.issubst ?sbs ?G ?D |- ett.isctx ?D =>
    now apply (ett_sanity.sane_issubst sbs G D)
  | H : ett.istype ?G ?A |- ett.isctx ?G =>
    now apply (ett_sanity.sane_istype G A)
  | H : ett.isterm ?G ?u ?A |- ett.isctx ?G =>
    now apply (ett_sanity.sane_isterm G u A)
  | H : ett.isterm ?G ?u ?A |- ett.istype ?G ?A =>
    now apply (ett_sanity.sane_isterm G u A)
  | H : ett.eqctx ?G ?D |- ett.isctx ?G =>
    now apply (ett_sanity.sane_eqctx G D)
  | H : ett.eqctx ?G ?D |- ett.isctx ?D =>
    now apply (ett_sanity.sane_eqctx G D)
  | H : ett.eqsubst ?sbs ?sbt ?G ?D |- ett.isctx ?G =>
    now apply (ett_sanity.sane_eqsubst sbs sbt G D)
  | H : ett.eqsubst ?sbs ?sbt ?G ?D |- ett.isctx ?D =>
    now apply (ett_sanity.sane_eqsubst sbs sbt G D)
  | H : ett.eqsubst ?sbs ?sbt ?G ?D |- ett.issubst ?sbs ?G ?D =>
    now apply (ett_sanity.sane_eqsubst sbs sbt G D)
  | H : ett.eqsubst ?sbs ?sbt ?G ?D |- ett.issubst ?sbt ?G ?D =>
    now apply (ett_sanity.sane_eqsubst sbs sbt G D)
  | H : ett.eqtype ?G ?A ?B |- ett.isctx ?G =>
    now apply (ett_sanity.sane_eqtype G A B)
  | H : ett.eqtype ?G ?A ?B |- ett.istype ?G ?A =>
    now apply (ett_sanity.sane_eqtype G A B)
  | H : ett.eqtype ?G ?A ?B |- ett.istype ?G ?B =>
    now apply (ett_sanity.sane_eqtype G A B)
  | H : ett.eqterm ?G ?u ?v ?A |- ett.isctx ?G =>
    now apply (ett_sanity.sane_eqterm G u v A)
  | H : ett.eqterm ?G ?u ?v ?A |- ett.istype ?G ?A =>
    now apply (ett_sanity.sane_eqterm G u v A)
  | H : ett.eqterm ?G ?u ?v ?A |- ett.isterm ?G ?u ?A =>
    now apply (ett_sanity.sane_eqterm G u v A)
  | H : ett.eqterm ?G ?u ?v ?A |- ett.isterm ?G ?v ?A =>
    now apply (ett_sanity.sane_eqterm G u v A)
  end.

(* A tactic to change between ett and ptt *)
Ltac pex :=
  match goal with
  (* Prove in ETT instead of PTT *)
  | |- ptt.isctx _         => apply ett2ptt.sane_isctx
  | |- ptt.issubst _ _ _   => apply ett2ptt.sane_issubst
  | |- ptt.istype _ _      => apply ett2ptt.sane_istype
  | |- ptt.isterm _ _ _    => apply ett2ptt.sane_isterm
  | |- ptt.eqctx _ _       => apply ett2ptt.sane_eqctx
  | |- ptt.eqsubst _ _ _ _ => apply ett2ptt.sane_eqsubst
  | |- ptt.eqtype _ _ _    => apply ett2ptt.sane_eqtype
  | |- ptt.eqterm _ _ _ _  => apply ett2ptt.sane_eqterm
  (* Prove in PTT instead of ETT *)
  | |- ett.isctx _         => apply ptt2ett.sane_isctx
  | |- ett.issubst _ _ _   => apply ptt2ett.sane_issubst
  | |- ett.istype _ _      => apply ptt2ett.sane_istype
  | |- ett.isterm _ _ _    => apply ptt2ett.sane_isterm
  | |- ett.eqctx _ _       => apply ptt2ett.sane_eqctx
  | |- ett.eqsubst _ _ _ _ => apply ptt2ett.sane_eqsubst
  | |- ett.eqtype _ _ _    => apply ptt2ett.sane_eqtype
  | |- ett.eqterm _ _ _ _  => apply ptt2ett.sane_eqterm
  end.

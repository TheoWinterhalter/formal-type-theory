Require Import syntax.
Require Import tt.
Require Import config_tactics.
Require eitt.

Axiom cheating : forall A : Type, A.
Definition todo {A} := cheating A.

Inductive ctxcoe : Type :=
  | ctxcoe_identity : ctxcoe

  | ctxcoe_ctxextend :
      forall c1 : ctxcoe, (* c1 : G ~~~> D *)
      forall c2 : tycoe,  (* for some G ⊢ A and D ⊢ B:
                             D ⊢ c2 : (act_type c1 A) ~~~> B *)
        ctxcoe (* G, A ~~~> D, B *)

with tycoe : Type :=
  | tycoe_identity : tycoe
  | tycoe_prod :
      forall (A1 B1 : type) (* G, A1 ⊢ B1 *)
             (A2 B2 : type) (* G, A2 ⊢ B2 *)
             (cA : tycoe) (* G ⊢ cA : A1 ~~~> A2 *)
             (cB : tycoe), (* G, A2 ⊢ (act_type (ctxcoe_ctxextend ctxcoe_identity c1) B1) ~~~> B2 *)
        tycoe (* Prod A1 B1 ~~~> Prod A2 B2 *)
  | tycoe_id : tycoe -> termcoe -> termcoe -> tycoe

with termcoe : Type :=
  | termcoe_identity : termcoe
  | termcoe_reflection : forall (A : type) (u v p : term), termcoe.


(* Computation of inverses of coercions *)

Fixpoint inv_ctxcoe (crc : ctxcoe) : ctxcoe :=
  match crc with
  | ctxcoe_identity => ctxcoe_identity
  | ctxcoe_ctxextend c1 c2 => ctxcoe_ctxextend (inv_tycoe c1)
  end

with inv_tycoe (crt : tycoe) : tycoe :=
  match crt with
  | tycoe_identity => tycoe_identity
  | tycoe_prod A1 B1 A2 B2 cA cB =>
    tycoe_prod A2 B2 A1 B1 (inv_tycoe cA) (inv_tycoe cB)
  | tycoe_id cA cu cv => tycoe_id (inv_tycoe cA) (inv_termcoe cu) (inv_termcoe cv)
  end

with inv_termcoe (crtt : termcoe) : termcoe :=
  match crtt with
  | termcoe_identity => termcoe_identity
  | termcoe_reflection A u v p =>
    termcoe_reflection A v u (j A u (Id A (var 1) u) (refl A u) v p)
  end.



(* Action of coercions on expressions *)

Fixpoint act_subst_left (crc : ctxcoe) (sbs : substitution) : substitution :=
  match crc with
    | ctx_id => sbs
  end.

Fixpoint act_subst_right (crc : ctxcoe) (sbs : substitution) : substitution :=
  match crc with
    | ctx_id => sbs
  end.

Definition act_subst (crc1 crc2 : ctxcoe) (sbs : substitution) :=
  act_subst_left crc1 (act_subst_right crc2 sbs).

Fixpoint act_type (crc : ctxcoe) (A : type) :=
  match crc with
  | ctx_id => A
  end.

Fixpoint act_term_ctx (crc : ctxcoe) (u : term) : term :=
  match crc with
  | ctx_id => u
  end.

Fixpoint act_term_type (crc : tycoe) (u : term) : term :=
  match crc with
  | tycoe_identity => u
  | tycoe_prod A1 B1 A2 B2 cA cB =>
    (* The situation:
       G ⊢ A1
       G, A1 ⊢ B1
       G ⊢ A2
       G, A2 ⊢ B2
       G ⊢ cA : A1 ⇒ A2
       G, A2 ⊢ cB : (act_(ctxextend G cA) B1) ⇒ B2
     *)
    lam
      A2
      B2
      (act_term_type cB (app u A1 B1 ()))

  | tycoe_id cA cu cv => todo (* I'm a bit lost *)
  end.

Definition act_term (crc : ctxcoe) (crt : tycoe) (u : term) : term :=
  act_term_type crt (act_term_ctx crc u).

Inductive isctxcoe : ctxcoe -> context -> context -> Type :=
  | isctxcoe_identity : forall G, eitt.isctx G -> isctxcoe ctxcoe_identity G G.

Inductive istypecoe : tycoe -> type -> type -> Type :=
  | istycoe_identity : forall {G A B}, eitt.eqtype G A B -> istypecoe tycoe_identity A B.

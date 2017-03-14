Require Import syntax.
Require Import tt.
Require Import config_tactics.
Require eitt.

Axiom cheating : forall A : Type, A.
Definition todo {A} := cheating A.
Ltac todo := apply cheating.

(* Inductive ctxcoe : Type := *)

(*   | ctxcoe_identity : ctxcoe *)

(*   | ctxcoe_ctxextend : *)
(*       forall c1 : ctxcoe,   (* c1 : Γ ~~~> Δ *) *)
(*       forall c2 : tycoe c1, (* c2 : Γ ⊢ A ~~~> Δ ⊢ B *) *)
(*         ctxcoe (* Γ, A ~~~> Δ,B *) *)

(* with tycoe : ctxcoe -> Type := *)

(*   | tycoe_identity : tycoe ctxcoe_identity (* I don't know how to make sense of *)
(*                                               it otherwise *) *)

(*   | tycoe_prod (A1 B1 A2 B2 : type) *)
(*                (c : ctxcoe) *)
(*                (cA : tycoe c) *)
(*                (cB : tycoe (ctxcoe_ctxextend c cA)) : tycoe c *)

(*   | tycoe_id (c : ctxcoe) (cA : tycoe c) (cu cv : termcoe c cA) : tycoe c *)

(* with termcoe : forall (c : ctxcoe), tycoe c -> Type := *)

(*   | termcoe_identity : termcoe ctxcoe_identity tycoe_identity *)

(*   | termcoe_reflection (A : type) (u v p : term) : *)
(*       termcoe ctxcoe_identity tycoe_identity (* For now at least *) *)
(* . *)

(* The coercions can't have coercions as index in the current coq.
   The information of one coercion being over another will be found in
   the derivation that a coercion is a well-behaved one. *)
Inductive ctxcoe : Type :=

  | ctxcoe_identity : ctxcoe

  | ctxcoe_ctxextend :
      forall c1 : ctxcoe, (* c1 : Γ ~~~> Δ *)
      forall c2 : tycoe,  (* c2 : Γ ⊢ A ~~~> Δ ⊢ B *)
        ctxcoe (* Γ, A ~~~> Δ,B *)

with tycoe : Type :=

  | tycoe_identity : tycoe

  | tycoe_prod (A1 B1 A2 B2 : type)
               (c : ctxcoe)
               (cA : tycoe)
               (cB : tycoe) : tycoe

  | tycoe_id (c : ctxcoe) (cA : tycoe) (cu cv : termcoe) : tycoe

with termcoe : Type :=

  | termcoe_identity : termcoe

  | termcoe_reflection (A : type) (u v p : term) : termcoe
.

Inductive isctxcoe : ctxcoe -> context -> context -> Type :=

  | isctxcoe_identity :
      forall G,
        eitt.isctx G ->
        isctxcoe ctxcoe_identity G G

  | isctxcoe_ctxextend :
      forall G D A B c1 c2,
        isctxcoe c1 G D ->
        istycoe c1 G D c2 A B ->
        isctxcoe (ctxcoe_ctxextend c1 c2) (ctxextend G A) (ctxextend D B)

with istycoe : ctxcoe -> context -> context -> tycoe -> type -> type -> Type :=

  | istycoe_identity :
      forall G A,
        eitt.istype G A ->
        istycoe ctxcoe_identity G G tycoe_identity A A

  | istycoe_prod :
      forall G D A1 B1 A2 B2 c cA cB,
        isctxcoe c G D ->
        istycoe c G D cA A1 A2 ->
        istycoe (ctxcoe_ctxextend c cA) (ctxextend G A1) (ctxextend D A2)
                cB B1 B2 ->
        istycoe c G D
                (tycoe_prod A1 B1 A2 B2 c cA cB) (Prod A1 B1) (Prod A2 B2)

  | istycoe_id :
      forall G D A1 u1 v1 A2 u2 v2 c cA cu cv,
        isctxcoe c G D ->
        istycoe c G D cA A1 A2 ->
        istermcoe c G D cA A1 A2 cu u1 u2 ->
        istermcoe c G D cA A1 A2 cv v1 v2 ->
        istycoe c G D (tycoe_id c cA cu cv) (Id A1 u1 v1) (Id A2 u2 v2)

with istermcoe : ctxcoe -> context -> context ->
                 tycoe -> type -> type ->
                 termcoe -> term -> term -> Type :=

  | istermcoe_identity :
      forall G u A,
        eitt.isterm G u A ->
        istermcoe ctxcoe_identity G G
                  tycoe_identity A A
                  termcoe_identity u u

  | istermcoe_reflection :
      forall G A u v p w,
        eitt.isterm G p (Id A u v) ->
        eitt.isterm G w (reflective A) -> (* When did reflective A
                                            become a type?! *)
        istermcoe ctxcoe_identity G G
                  tycoe_identity A A
                  (termcoe_reflection A u v p) u v
.

(* Computation of inverses of coercions *)

Fixpoint inv_ctxcoe (crc : ctxcoe) : ctxcoe :=
  match crc with
  | ctxcoe_identity => ctxcoe_identity
  | ctxcoe_ctxextend c1 c2 => ctxcoe_ctxextend (inv_ctxcoe c1) (inv_tycoe c2)
  end

with inv_tycoe (crt : tycoe) : tycoe :=
  match crt with
  | tycoe_identity => tycoe_identity
  | tycoe_prod A1 B1 A2 B2 c cA cB =>
    tycoe_prod A2 B2 A1 B1 (inv_ctxcoe c) (inv_tycoe cA) (inv_tycoe cB)
  | tycoe_id c cA cu cv =>
    tycoe_id (inv_ctxcoe c) (inv_tycoe cA) (inv_termcoe cu) (inv_termcoe cv)
  end

with inv_termcoe (crtt : termcoe) : termcoe :=
  match crtt with
  | termcoe_identity => termcoe_identity
  | termcoe_reflection A u v p =>
    let weak :=
      sbweak (Id (Subst A (sbweak A))
                 (subst u (sbweak A))
                 (var 0))
    in
    let Aww := (Subst (Subst A (sbweak A)) weak) in
    let uww := (subst (subst u (sbweak A)) weak) in
    termcoe_reflection A v u (j A u (Id Aww (var 1) uww) (refl A u) v p)
  end.

(* Now we should prove that taking the inverse preserves well-behavior. *)
Fixpoint isctxcoe_inv {c G D} (H : isctxcoe c G D) {struct H} :
  isctxcoe (inv_ctxcoe c) D G

with istycoe_inv {c G D cT A B} (H : istycoe c G D cT A B) {struct H} :
  istycoe (inv_ctxcoe c) D G (inv_tycoe cT) B A

with istermcoe_inv
  {c G D cT A B ct u v} (H : istermcoe c G D cT A B ct u v) {struct H} :
  istermcoe (inv_ctxcoe c) D G (inv_tycoe cT) B A (inv_termcoe ct) v u.
Proof.
  - { destruct H.

      (* isctxcoe_identity *)
      - now constructor.

      (* isctxcoe_ctxextend *)
      - simpl. constructor.
        + apply (isctxcoe_inv _ _ _ H).
        + apply (istycoe_inv _ _ _ _ _ _ i).
    }

  - { destruct H.

      (* istycoe_identity *)
      - now constructor.

      (* istycoe_prod *)
      - simpl. constructor.
        + apply (isctxcoe_inv _ _ _ i).
        + apply (istycoe_inv _ _ _ _ _ _ H).
        + apply (istycoe_inv _ _ _ _ _ _ H0).

      (* istycoe_id *)
      - simpl. constructor.
        + apply (isctxcoe_inv _ _ _ i).
        + apply (istycoe_inv _ _ _ _ _ _ H).
        + apply (istermcoe_inv _ _ _ _ _ _ _ _ _ i0).
        + apply (istermcoe_inv _ _ _ _ _ _ _ _ _ i1).
    }

  - { destruct H.

      (* istermcoe_identity *)
      - now constructor.

      (* istermcoe_reflection *)
      - simpl. econstructor.
        + ceapply TermTyConv.
          * ceapply TermJ.
            -- todo. (* Inversion *)
            -- capply TyId.
               ++ ceapply TermVarSucc.
                  ** capply TermVarZero.
                     todo. (* Inversion *)
                  ** capply TyId.
                     --- ceapply TermSubst.
                         +++ capply SubstWeak.
                             todo. (* Inversion *)
                         +++ todo. (* Inversion *)
                     --- capply TermVarZero.
                         todo. (* Inversion *)
               ++ ceapply TermSubst.
                  ** capply SubstWeak.
                     capply TyId.
                     --- ceapply TermSubst.
                         +++ capply SubstWeak.
                             todo. (* Inversion *)
                         +++ todo. (* Inversion *)
                     --- capply TermVarZero.
                         todo. (* Inversion *)
                  ** ceapply TermSubst.
                     +++ capply SubstWeak.
                         todo. (* Inversion *)
                     +++ todo. (* Inversion *)
            -- ceapply TermTyConv.
               ++ capply TermRefl.
                  todo. (* Inversion *)
               ++ todo.
            -- todo. (* Inversion *)
            -- assumption.
          * todo.
        + eassumption.
    }
Qed.



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

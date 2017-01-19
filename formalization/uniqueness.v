(* Uniqueness of typing. *)

Require Import syntax.
Require ett ptt.
Require ptt2ett ett2ptt.
Require ett_sanity ptt_sanity.
(* Require Import sanity. *)

(* Auxiliary admissibility lemmas. *)

(* Lemma eqctx_sym {G D} : eqctx G D -> eqctx D G. *)
(* Proof. *)
(*   intros [|? ? ? ?]. *)
(*   - apply EqCtxEmpty. *)
(*   - now apply EqCtxExtend, EqTySym. *)
(* Defined. *)

(* Lemma eqctx_refl G : isctx G -> eqctx G G. *)
(* Proof. *)
(*   intros [|? ? ? ?]. *)
(*   - apply EqCtxEmpty. *)
(*   - now apply EqCtxExtend, EqTyRefl. *)
(* Defined. *)

(* Lemma eqctx_trans G D E : *)
(*   eqctx G D -> eqctx D E -> eqctx G E. *)
(* Proof. *)
(*   intros [|? ? ? ?]. *)
(*   - intro H ; exact H. *)
(*   - intro H. *)
(*     inversion H. *)
(*     apply EqCtxExtend. *)
(*     eapply EqTyTrans. *)
(*     + eassumption. *)
(*     + assumption. *)
(* Defined. *)

(* Auxiliary inversion lemmas. *)

Fixpoint eqctx_ctxextend G A G' A'
         (H : ett.eqctx (ctxextend G A) (ctxextend G' A')) {struct H} :
  (ett.eqctx G G' * ett.eqtype G A A')%type.
Proof.
  inversion H ; subst.
  - split.
    + apply ett.CtxRefl.
      admit. (* sanity and inversion *)
    + apply ett.EqTyRefl.
      admit. (* sanity and inversion *)
  - destruct (eqctx_ctxextend G' A' G A H0).
    split.
    + now apply ett.CtxSym.
    + apply ett.EqTySym.
      eapply ett.EqTyCtxConv ; eassumption.
  - (* destruct (eqctx_ctxextend _ _ _ _ H0). *)
    (* Do we need another inversion lemma here as well? *)
    admit.
  - split ; assumption.
Admitted.


(* It looks like we need to strengthen some inference
   rules, as follows: *)

Lemma substCtxConv' :
  forall G G' D sbs (E : ett.eqctx G' G),
    ett.issubst sbs G D -> ett.issubst sbs G' D.
Proof.
  intros G G' D sbs E H.
  eapply ett.SubstCtxConv.
  - eassumption.
  - now apply ett.CtxSym.
  - apply ett.CtxRefl.
    now apply (ett_sanity.sane_issubst sbs G D).
Defined.

(* Hypothesis eqCtxExtend' : *)
(*   forall {G D A B}, *)
(*     eqctx G D -> *)
(*     eqtype G A B -> *)
(*     eqctx (ctxextend G A) (ctxextend D B). *)

(* Hypothesis eqTyCongWeak' : *)
(*   forall { G A A' B B' }, *)
(*   eqtype G A A' -> *)
(*   eqtype G B B' -> *)
(*   eqtype (ctxextend G A) (Subst B (sbweak G A)) (Subst B' (sbweak G A')). *)

(* Hypothesis eqTyCongZero' : *)
(*   forall {G1 G2 A1 A2 B1 B2 u1 u2}, *)
(*     eqctx G1 G2 -> *)
(*     eqtype G1 A1 B1 -> *)
(*     eqterm G1 u1 u2 A1 -> *)
(*     eqtype (ctxextend G1 A1) A2 B2 -> *)
(*     eqtype G1 *)
(*            (Subst A2 (sbzero G1 A1 u1)) *)
(*            (Subst B2 (sbzero G2 B1 u2)). *)

(* Hypothesis eqTyCongShift' : *)
(*   forall {G1 G2 D A1 A2 B1 B2 sbs}, *)
(*     eqctx G1 G2 -> *)
(*     issubst sbs G1 D -> *)
(*     eqtype D A1 A2 -> *)
(*     eqtype (ctxextend D A1) B1 B2 -> *)
(*     eqtype (ctxextend G1 (Subst A1 sbs)) *)
(*            (Subst B1 (sbshift G1 A1 sbs)) *)
(*            (Subst B2 (sbshift G2 A2 sbs)). *)

(* A hack to be able to allow cases and still have Coq verify
   that the fixpoints are well-defined. *)
Hypothesis temporary :
  forall {A}, A.

Ltac todo := exact temporary.

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

(* Tactics for dealing with the conversion cases. *)

Ltac doTyConv unique_term' :=
  eapply ett.EqTyTrans ;
  [ eapply unique_term' ;
    [ ehyp
    | hyp ]
  | eapply ett.EqTyCtxConv ;
    [ ehyp
    | hyp ] ].

Ltac doCtxConv D' unique_term' :=
  eapply unique_term' ;
  [ ehyp
  | apply (@ett.CtxTrans _ D') ; hyp ].

(* The version of the theorem that allows variation of the context. *)

Fixpoint unique_term_ctx G u A (H1 : ptt.isterm G u A) {struct H1}:
  forall B D,
    ptt.isterm D u B ->
    ptt.eqctx D G ->
    ett.eqtype G A B

with unique_subst G D1 sbs (H1 : ptt.issubst sbs G D1) {struct H1}:
  forall D2 (H2 : ptt.issubst sbs G D2),
    ett.eqctx D1 D2.

Proof.
  (* unique_term *)
  { destruct H1 ;
    simple refine (fix unique_term'' B' D' H2' H3' {struct H2'} := _) ;
    pose (
      unique_term' B' D' H1 H2 :=
        unique_term'' B' D'
                      (* (ett2ptt.sane_isterm D' _ B' H1) *)
                      H1
                      (ett2ptt.sane_eqctx D' _ H2)
    ) ;
    pose (
      unique_term_ctx' G u A H1 B D H2 H3 :=
        unique_term_ctx G u A
                        (* (ett2ptt.sane_isterm G u A H1) *)
                        H1
                        B D
                        (ett2ptt.sane_isterm D u B H2)
                        (ett2ptt.sane_eqctx D G H3)
    ) ;
    pose (
      unique_subst' G D1 sbs H1 D2 H2 :=
        unique_subst G D1 sbs
                     (* (ett2ptt.sane_issubst sbs G D1 H1) *)
                     H1
                     D2
                     (ett2ptt.sane_issubst sbs G D2 H2)
    ).

    (* H1: TermTyConv *)
    - {
        apply (@ett.EqTyTrans G _ A B').
        + apply ett.EqTySym. hyp.
        + eapply (unique_term_ctx G u A) ; eassumption.
      }

    (* TermCtxConv *)
    - {
        eapply ett.EqTyCtxConv.
        - eapply unique_term_ctx'.
          + ehyp.
          + ehyp.
          + apply (@ett.CtxTrans _ D).
            * hyp.
            * apply ett.CtxSym. hyp.
        - hyp.
      }

    (* TermSubst *)
    - { inversion_clear H2'.
        - doTyConv unique_term'.
        - doCtxConv D' unique_term'.

        - eapply ett.CongTySubst.
          + eapply ett.SubstRefl. ehyp.
          + eapply (unique_term_ctx' _ u).
            * hyp.
            * ehyp.
            * { apply ett.CtxSym.
                apply (unique_subst' G _ sbs).
                - hyp.
                - eapply substCtxConv'.
                  + eapply ett.CtxSym.
                    ehyp.
                  + hyp.
              }
      }

    (* TermVarZero *)
    - { inversion H2'.
        - doTyConv unique_term'.
        - doCtxConv D' unique_term'.

        - { assert (L : ett.eqctx (ctxextend G0 A0) (ctxextend G A)).
            - rewrite H1. hyp.
            - destruct (eqctx_ctxextend _ _ _ _  L) as [E M].
              eapply ett.CongTySubst.
              + eapply ett.CongSubstWeak.
                * now apply ett.CtxSym.
                * apply ett.EqTySym.
                  eapply ett.EqTyCtxConv ; eassumption.
              + apply ett.EqTySym.
                eapply ett.EqTyCtxConv ; eassumption.
          }
      }


    (* TermVarSucc *)
      - (* { inversion H2'. *)
        (*   - doTyConv unique_term'. *)
        (*   - doCtxConv D' unique_term'. *)

        (*   - { assert (L : eqctx (ctxextend G0 B0) (ctxextend G B)). *)
        (*       - now rewrite H2. *)
        (*       - destruct (eqctx_ctxextend _ _ _ _  L) as [E M]. *)
        (*         rewrite E in * |- *. *)
        (*         apply eqTyCongWeak'. *)
        (*         + now apply EqTySym. *)
        (*         + eapply (unique_term_ctx _ (var k)). *)
        (*           * assumption. *)
        (*           * eassumption. *)
        (*           * apply eqctx_refl. *)
        (*             now apply (@sane_isterm G A (var k)). *)
        (*     } *)
        (* } *)
        todo.

      (* TermAbs *)
      - (* { inversion_clear H2'. *)
        (*   - doTyConv unique_term'. *)
        (*   - doCtxConv D' unique_term'. *)

        (*   - apply EqTyRefl. *)
        (*     + apply TyProd. *)
        (*       * assumption. *)
        (*       * now apply (@sane_isterm (ctxextend G A) B u). *)
        (* } *)
        todo.

      (* TermApp *)
      - (* { inversion_clear H2'. *)
        (*   - doTyConv unique_term'. *)
        (*   - doCtxConv D' unique_term'. *)

        (*   - { apply eqTyCongZero'. *)
        (*       - now apply eqctx_sym. *)
        (*       - now apply EqTyRefl, (@sane_isterm G A v). *)
        (*       - now apply EqRefl. *)
        (*       - now apply EqTyRefl. *)
        (*     } *)
        (* } *)
        todo.

      (* TermRefl *)
      - (* { inversion_clear H2'. *)
        (*   - doTyConv unique_term'. *)
        (*   - doCtxConv D' unique_term'. *)

        (*   - apply EqTyRefl, TyId. *)
        (*     + now apply (@sane_isterm G A u). *)
        (*     + assumption. *)
        (*     + assumption. *)
        (* } *)
        todo.

      (* TermJ *)
      - (* { inversion_clear H2'. *)
        (*   - doTyConv unique_term'. *)
        (*   - doCtxConv D' unique_term'. *)

        (*   - { apply eqTyCongZero'. *)
        (*       + now apply eqctx_sym. *)
        (*       + now apply EqTyRefl, TyId. *)
        (*       + apply EqRefl. *)
        (*         eapply TermCtxConv; eassumption. *)
        (*       + { apply temporary. } *)
        (*     } *)
        (* } *)
        todo.

      (* TermExfalso *)
      - (* { inversion_clear H2'. *)
        (*   - doTyConv unique_term'. *)
        (*   - doCtxConv D' unique_term'. *)

        (*   - { apply EqTyRefl. *)
        (*       eapply TyCtxConv. *)
        (*       + eassumption. *)
        (*       + assumption. } *)
        (* } *)
        todo.

      (* TermUnit *)
      - (* { inversion_clear H2'. *)
        (*   - doTyConv unique_term'. *)
        (*   - doCtxConv D' unique_term'. *)

        (*   - now apply EqTyRefl, TyUnit. *)
        (* } *)
        todo.

      (* TermTrue *)
      - (* { inversion_clear H2'. *)
        (*   - doTyConv unique_term'. *)
        (*   - doCtxConv D' unique_term'. *)

        (*   - now apply EqTyRefl, TyBool. *)
        (* } *)
        todo.

      (* TermFalse *)
      - (* { inversion_clear H2'. *)
        (*   - doTyConv unique_term'. *)
        (*   - doCtxConv D' unique_term'. *)

        (*   - now apply EqTyRefl, TyBool. *)
        (* } *)
        todo.

      (* TermCond *)
      - (* { inversion_clear H2'. *)
        (*   - doTyConv unique_term'. *)
        (*   - doCtxConv D' unique_term'. *)

        (*   - { apply eqTyCongZero'. *)
        (*       + now apply eqctx_sym. *)
        (*       + now apply EqTyRefl, TyBool, (@sane_isterm G Bool u). *)
        (*       + now apply EqRefl. *)
        (*       + now apply EqTyRefl. *)
        (*     } *)
        (* } *)
        todo.
  }

 (* unique_subst *)
 (* { intros D2 H2. *)
 (*   destruct H1. *)

 (*   (* H1: SubstZero *) *)
 (*   - { inversion_clear H2. *)
 (*       apply eqctx_refl, CtxExtend; now apply (@sane_isterm G A u). *)
 (*     } *)

 (*   (* H1: SubstWeak *) *)
 (*   - { inversion_clear H2. *)
 (*       now apply eqctx_refl, (@sane_istype D2 A). *)
 (*     } *)

 (*   (* H2: SubstShift *) *)
 (*   - { inversion_clear H2. *)
 (*       apply eqCtxExtend'. *)
 (*       apply (unique_subst G _ sbs). *)
 (*       + assumption. *)
 (*       + assumption. *)
 (*       + now apply EqTyRefl. *)
 (*     } *)
 (* } *)
  todo.

Defined.

(* The main theorem as it will probably be used. *)
(* Corollary unique_term {G A B u} : *)
(*   isterm G u A -> *)
(*   isterm G u B -> *)
(*   eqtype G A B. *)

(* Proof. *)
(*   intros H1 H2. *)
(*   eapply unique_term_ctx. *)
(*   - eassumption. *)
(*   - eassumption. *)
(*   - now apply eqctx_refl, (@sane_isterm G A u). *)
(* Defined. *)

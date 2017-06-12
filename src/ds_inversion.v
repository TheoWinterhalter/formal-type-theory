(* Daring syntax inversion

   The purpose of this file is to provide the inversion lemmata that are
   required by sanity on daring syntax.
   These lemmata are proven only in the case of paranoid rules.
*)

Require config.
Require wfconfig.
Require Import daring_syntax.
Require Import config_tactics.

Require Import Coq.Program.Equality.

Section DaringSyntaxInversion.

Open Scope type_scope.

Local Instance hasPrecond : config.Precond := {|
  config.precondFlag := config.Yes
|}.
Context {ConfigReflection : config.Reflection}.
Context {ConfigSimpleProducts : config.SimpleProducts}.
Context {ConfigProdEta : config.ProdEta}.
Context {ConfigUniverses : config.Universes}.
Context {ConfigWithProp : config.WithProp}.
Context {ConfigWithJ : config.WithJ}.
Context {ConfigEmpty : config.WithEmpty}.
Context {ConfigUnit : config.WithUnit}.
Context {ConfigBool : config.WithBool}.
Context {ConfigPi : config.WithPi}.

Definition CtxExtendInversion G A (H : isctx (ctxextend G A)) :
  isctx G * istype G A.
Proof.
  config inversion H. easy.
Defined.

Axiom admit : forall {A}, A.
Tactic Notation "admit" := (exact admit).

Lemma SubstIdInversion {Γ Δ A u v C σ} :
  issubst σ Γ Δ ->
  σ C = Id A u v ->
  { A' : term &
  { u' : term &
  { v' : term &
    (C = Id A' u' v') *
    istype Δ (Id A' u' v')
  } } }.
Proof.
  intros h1 h2.
  dependent induction h1 ; doConfig.

  - { simpl in *.
      dependent induction C ; simpl in h2 ; try discriminate.
      - repeat eexists. admit.
      - admit.
    }

  - { simpl in *.
      dependent induction C ; simpl in h2 ; try discriminate.
      repeat eexists. admit.
    }

  - { simpl in *.
      dependent induction C ; simpl in h2 ; try discriminate.
      repeat eexists. admit.
    }

  - { simpl in *.
      dependent induction C ; simpl in h2 ; try discriminate.
      repeat eexists. admit.
    }

  - { simpl in *.
      dependent induction C ; simpl in h2 ; try discriminate.
      (* This case is really bothersome... *)
      all:admit.
    }
Abort.
(* There would be the option of having the substitution rules optional
   and replaced by some admissibility result whenever turned off.
 *)

Definition TermIdInversion G A u v U (H : isterm G (Id A u v) U) :
  forall {l}, eqtype G U (Uni l) ->
  isctx G * isterm G A U * istype G A * isterm G u A * isterm G v A.
Proof.
  intros l h.
  dependent induction H ; doConfig.

  - { repeat split.
      - assumption.
      - config apply @tt.TermTyConv with (A := A0).
        + pose (IHisterm A u v (eq_refl _) JMeq_refl l).
          apply p.
          (config apply @tt.EqTyTrans with (B := B)) ; try assumption.
          (* admit. *)
  (*       + assumption. *)
  (*       + assumption. *)
  (*       + assumption. *)
  (*       + assumption. *)
  (*     - pose (IHisterm A u v (eq_refl _) JMeq_refl l). now apply p. *)
  (*     - pose (IHisterm A u v). now apply p. *)
  (*   } *)

  (* - { repeat split. *)
  (*     - assumption. *)
  (*     - config apply @tt.TermCtxConv with (G := G). *)
  (*       + now eapply @IHisterm with (A1 := A). *)
  (*       + assumption. *)
  (*       + assumption. *)
  (*       + assumption. *)
  (*       + assumption. *)
  (*     - config apply @tt.TermCtxConv with (G := G). *)
  (*       + pose (IHisterm A u v). now apply p. *)
  (*       + assumption. *)
  (*       + assumption. *)
  (*       + assumption. *)
  (*       + admit. (* We need to know that A is a type as well... *) *)
  (*     - config apply @tt.TermCtxConv with (G := G). *)
  (*       + pose (IHisterm A u v). now apply p. *)
  (*       + assumption. *)
  (*       + assumption. *)
  (*       + assumption. *)
  (*       + admit. *)
  (*   } *)

  (* - admit. (* Substitutions *) *)

  (* - { repeat split ; assumption. } *)
Abort.

Definition TyIdInversion G A u v (H : istype G (Id A u v)) :
  isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  dependent induction H ; doConfig.

  - { repeat split.

      - assumption.
      - apply @tt.TyCtxConv with (G := G) ; auto.
        now eapply IHistype.
      - apply @tt.TermCtxConv with (G := G) ; auto.
        + now eapply @IHistype with (u0 := u) (v0 := v).
        + now config eapply @IHistype with (u0 := u) (v0 := v).
      - apply @tt.TermCtxConv with (G := G) ; auto.
        + now eapply @IHistype with (u0 := u) (v0 := v).
        + now config eapply @IHistype with (u0 := u) (v0 := v).
    }

  - (* { repeat split. *)

(*       - assumption. *)
(*       - (* Maybe we need some lemma to conclude that Subst A0 σ = Id A u v *) *)
(* (*            implies A0 is some Id as well. *) *)
    admit.

  - { repeat split.
      - assumption.
      - assumption.
      - assumption.
      - assumption.
    }

  - { cbv in x. subst.
Abort.

Fixpoint TyIdInversion G A u v (H : istype G (Id A u v)) {struct H} :
  isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  inversion H ; doConfig.

  - { split ; [(split ; [split | idtac]) | idtac].

      - assumption.
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply TyIdInversion with (u := u) (v := v).
      - apply @tt.TermCtxConv with (G := G0) ; auto.
        + now apply TyIdInversion with (u := u) (v:= v).
        + now config apply TyIdInversion with (u := u) (v:= v).
      - apply @tt.TermCtxConv with (G := G0) ; auto.
        + now apply TyIdInversion with (u := u) (v:= v).
        + now config apply TyIdInversion with (u := u) (v:= v).
    }

  - { split ; [(split ; [split | idtac]) | idtac].

      - assumption.
      - admit.
      - admit.
      - admit.
    }

  - { split ; [(split ; [split | idtac]) | idtac].
      - assumption.
      - assumption.
      - assumption.
      - assumption.
    }

  - { split ; [(split ; [split | idtac]) | idtac].
      - assumption.
      - cbv in H2. subst. inversion X.
        + admit.
        + admit.
        + admit.
        + admit.
      (* Does this ever end?
         Maybe we would like as well to limit the typing rules of istype
         to always be about TyEl... But this doesn't play well when the flag
         is off...
         Any chance of admissibility of some rules to remove them from
         inversion?
       *)
      - admit.
      - admit.
    }

Defined.

Fixpoint TyProdInversion G A B (H : istype G (Prod A B)) {struct H} :
  isctx G * istype G A * istype (ctxextend G A) B.
Proof.
  inversion H ; doConfig.

  - { split ; [ split | idtac ].
      - assumption.
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TyProdInversion G0 A B).
      - apply @tt.TyCtxConv with (G := ctxextend G0 A).
        + now apply (TyProdInversion G0 A B).
        + apply @tt.EqCtxExtend ; auto.
          * now capply (TyProdInversion G0 A B).
          * now capply (TyProdInversion G0 A B).
          * capply @tt.EqTyRefl ; auto.
            now apply (TyProdInversion G0 A B).
        + capply @tt.CtxExtend ; auto.
          now apply (TyProdInversion G0 A B).
        + capply @tt.CtxExtend.
          * assumption.
          * apply @tt.TyCtxConv with (G := G0) ; auto.
            now apply (TyProdInversion G0 A B).
    }

  - admit.

  - { split ; [ split | idtac ].
      - assumption.
      - assumption.
      - assumption.
    }

  - { split ; [ split | idtac ].
      - assumption.
      - admit.
      - admit.
    }
Defined.

Fixpoint TySimProdInversion G A B (H : istype G (SimProd A B)) {struct H} :
  isctx G * istype G A * istype G B.
Proof.
  inversion H ; doConfig.

  - { split ; [ split | .. ].
      - assumption.
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TySimProdInversion G0 A B).
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TySimProdInversion G0 A B).
    }

  - admit.

  - { split ; [ split | .. ] ; assumption. }

  - admit.
Defined.

Local Instance LocSyntax : config.Syntax := Syntax.

Local Instance CtxExtendInversionInstance : wfconfig.CtxExtendInversionClass
  := {| wfconfig.CtxExtendInversion := CtxExtendInversion |}.

Local Instance TyIdInversionInstance : wfconfig.TyIdInversionClass
  := {| wfconfig.TyIdInversion := TyIdInversion |}.

Local Instance TyProdInversionInstance : wfconfig.TyProdInversionClass
  := {| wfconfig.TyProdInversion h := TyProdInversion |}.

Local Instance TySimProdInversionInstance : wfconfig.TySimProdInversionClass
  := {| wfconfig.TySimProdInversion h := TySimProdInversion |}.

End DaringSyntaxInversion.

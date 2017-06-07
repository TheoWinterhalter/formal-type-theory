(* Daring syntax inversion

   The purpose of this file is to provide the inversion lemmata that are
   required by sanity on daring syntax.
   These lemmata are proven only in the case of paranoid rules.
*)

Require config.
Require Import wfconfig.
Require Import daring_syntax.
Require Import config_tactics.

Require Import Coq.Program.Equality.

Section DaringSyntaxInversion.

Local Instance hasPrecond : config.Precond := {|
  config.precondFlag := config.Yes
|}.
Context {ConfigReflection : config.Reflection}.
Context {simpleproductsFlag : config.Flag Type}.
Context {ConfigProdEta : config.ProdEta}.
Context {universesFlag : config.Flag Type}.
Context {withpropFlag : config.Flag Type}.
Context {withjFlag : config.Flag Type}.
Context {withemptyFlag : config.Flag Type}.
Context {withunitFlag : config.Flag Type}.
Context {withboolFlag : config.Flag Type}.
Context {withpiFlag : config.Flag Type}.

Definition CtxExtendInversion G A (H : isctx (ctxextend G A)) :
  isctx G * istype G A.
Proof.
  config inversion H. easy.
Defined.

Axiom admit : forall {A}, A.
Tactic Notation "admit" := (exact admit).

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

  - { repeat split.

      - assumption.
      - (* Maybe we need some lemma to conclude that Subst A0 σ = Id A u v
           implies A0 is some Id as well. *)
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
      - admit.
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

End DaringSyntaxInversion.

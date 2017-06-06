(* Paranoid syntax inversion

   The purpose of this file is to provide the inversion lemmata that are
   required by sanity on paranoid syntax.
*)

Require config.
Require Import wfconfig.
Require Import paranoid_syntax.
Require Import config_tactics.

Section ParanoidSyntaxInversion.

Context {ConfigPrecond : config.Precond}.
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

(* TODO: Find a way to have isctx refer to a type theory with paranoidsyntax.
   Besides, the flags up here should probably be type classes as well.
*)

Definition CtxExtendInversion G A (H : isctx (ctxextend G A)) :
  isctx G * istype G A.
Proof.
  config inversion H. split.
  - admit. (* Problem! Do we need the paranoid version for inversion?
              In a way it should be enough for ett2ptt. *)
  - assumption.
(* Defined. *)
Admitted.

Fixpoint TyIdInversion G A u v (H : istype G (Id A u v)) {struct H} :
  isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  inversion H ; doConfig.

  - { split ; [(split ; [split | idtac]) | idtac].

      - (* assumption. *) admit.
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
      - (* assumption. *) admit.
      - (* assumption. *) admit.
      - assumption.
      - assumption.
    }

(* Defined. *)
Admitted.

Fixpoint TyProdInversion G A B (H : istype G (Prod A B)) {struct H} :
  isctx G * istype G A * istype (ctxextend G A) B.
Proof.
  inversion H ; doConfig.

  - { split ; [ split | idtac ].
      - (* assumption. *) admit.
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TyProdInversion G0 A B).
      - apply @tt.TyCtxConv with (G := ctxextend G0 A).
        + now apply (TyProdInversion G0 A B).
        + (* WHY? *)
          apply tt.EqCtxExtend ; auto.
          * now capply (TyProdInversion G0 A B).
          * now capply (TyProdInversion G0 A B).
          * capply EqTyRefl ; auto.
            now apply (TyProdInversion G0 A B).
        + capply CtxExtend ; auto.
          now apply (TyProdInversion G0 A B).
        + capply CtxExtend.
          * assumption.
          * apply @TyCtxConv with (G := G0) ; auto.
            now apply (TyProdInversion G0 A B).
    }

  - { split ; [ split | idtac ].
      - assumption.
      - assumption.
      - assumption.
    }
Defined.

Fixpoint TySimProdInversion G A B (H : istype G (SimProd A B)) {struct H} :
  isctx G * istype G A * istype G B.
Proof.
  inversion H ; doConfig.

  - { split ; [ split | .. ].
      - assumption.
      - apply @TyCtxConv with (G := G0) ; auto.
        now apply (TySimProdInversion G0 A B).
      - apply @TyCtxConv with (G := G0) ; auto.
        now apply (TySimProdInversion G0 A B).
    }

  - { split ; [ split | .. ] ; assumption. }
Defined.

End ParanoidSyntaxInversion.

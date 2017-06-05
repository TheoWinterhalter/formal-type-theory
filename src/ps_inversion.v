(* Paranoid syntax inversion

   The purpose of this file is to provide the inversion lemmata that are
   required by sanity on paranoid syntax.
*)

Require config.
Require Import wfconfig.
Require Import paranoid_syntax tt.

Section ParanoidSyntaxInversion.

Context {ConfigPrecond : config.Precond}.
Context {ConfigReflection : config.Reflection}.
Context {simpleproductsFlag : Type}.
Context {ConfigProdEta : config.ProdEta}.
Context {universesFlag : Type}.
Context {withpropFlag : Type}.
Context {withjFlag : Type}.
Context {withemptyFlag : Type}.
Context {withunitFlag : Type}.
Context {withboolFlag : Type}.
Context {withpiFlag : Type}.

(* TODO: Find a way to have isctx refer to a type theory with paranoidsyntax.
   Besides, the flags up here should probably be type classes as well.
*)

Definition CtxExtendInversion G A (H : isctx (ctxextend G A)) :
  isctx G * istype G A.
Proof.
  config inversion_clear H. easy.
Defined.

Fixpoint TyIdInversion G A u v (H : istype G (Id A u v)) {struct H} :
  isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  inversion H ; doConfig.

  - { split ; [(split ; [split | idtac]) | idtac].

      - assumption.
      - apply @TyCtxConv with (G := G0) ; auto.
        now apply TyIdInversion with (u := u) (v := v).
      - apply @TermCtxConv with (G := G0) ; auto.
        + now apply TyIdInversion with (u := u) (v:= v).
        + now config apply TyIdInversion with (u := u) (v:= v).
      - apply @TermCtxConv with (G := G0) ; auto.
        + now apply TyIdInversion with (u := u) (v:= v).
        + now config apply TyIdInversion with (u := u) (v:= v).
    }

  - { split ; [(split ; [split | idtac]) | idtac].
      - assumption.
      - assumption.
      - assumption.
      - assumption.
    }

Defined.

Fixpoint TyProdInversion G A B (H : istype G (Prod A B)) {struct H} :
  isctx G * istype G A * istype (ctxextend G A) B.
Proof.
  inversion H ; doConfig.

  - { split ; [ split | idtac ].
      - assumption.
      - apply @TyCtxConv with (G := G0) ; auto.
        now apply (TyProdInversion G0 A B).
      - apply @TyCtxConv with (G := ctxextend G0 A).
        + now apply (TyProdInversion G0 A B).
        + apply EqCtxExtend ; auto.
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

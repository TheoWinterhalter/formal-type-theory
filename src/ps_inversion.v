(* Paranoid syntax inversion

   The purpose of this file is to provide the inversion lemmata that are
   required by sanity on paranoid syntax.
   These lemmata are proven only in the case of paranoid rules.
*)

Require config syntax.
Require invconfig.
Require Import paranoid_syntax.
Require Import config_tactics.

Section ParanoidSyntaxInversion.

Local Instance hasPrecond : config.Precond := {|
  config.precondFlag := config.Yes
|}.
Context `{configReflection : config.Reflection}.
Context `{configSimpleProducts : config.SimpleProducts}.
Context `{configProdEta : config.ProdEta}.
Context `{ConfigUniverses : config.Universes}.
Context `{ConfigWithProp : config.WithProp}.
Context `{ConfigId : config.IdentityTypes}.
Context `{ConfigWithJ : config.WithJ}.
Context `{ConfigEmpty : config.WithEmpty}.
Context `{ConfigUnit : config.WithUnit}.
Context `{ConfigBool : config.WithBool}.
Context `{ConfigPi : config.WithPi}.

Definition CtxExtendInversion G A (H : isctx (ctxextend G A)) :
  isctx G * istype G A.
Proof.
  config inversion H. easy.
Defined.

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
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TySimProdInversion G0 A B).
      - apply @tt.TyCtxConv with (G := G0) ; auto.
        now apply (TySimProdInversion G0 A B).
    }

  - { split ; [ split | .. ] ; assumption. }
Defined.

Local Instance LocSyntax : syntax.Syntax := Syntax.

Local Instance CtxExtendInversionInstance : invconfig.CtxExtendInversionClass
  := {| invconfig.CtxExtendInversion := CtxExtendInversion |}.

Local Instance TyIdInversionInstance : invconfig.TyIdInversionClass
  := {| invconfig.TyIdInversion := TyIdInversion |}.

Local Instance TyProdInversionInstance : invconfig.TyProdInversionClass
  := {| invconfig.TyProdInversion := TyProdInversion |}.

Local Instance TySimProdInversionInstance : invconfig.TySimProdInversionClass
  := {| invconfig.TySimProdInversion := TySimProdInversion |}.

End ParanoidSyntaxInversion.
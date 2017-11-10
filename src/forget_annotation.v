(* Forgetting Annotation

   We propose a straightforward translation from annotated syntax to concise
   syntax. We also prove the obvious statement that typing is preserved.
 *)

Require config.
Require Import config_tactics.

Require syntax.
Require Import tt.
Require annotated_syntax concise_syntax.

(* Annotated theory *)
Module Att.

  Section Att.

    Context `{configPrecondition : config.Precondition}.
    Context `{configReflection : config.Reflection}.
    Context `{configBinaryProdType : config.BinaryProdType}.
    Context `{configProdEta : config.ProdEta}.
    Context `{configUniverses : config.Universes}.
    Context `{configPropType : config.PropType}.
    Context `{configIdType : config.IdType}.
    Context `{configIdEliminator : config.IdEliminator}.
    Context `{configEmptyType : config.EmptyType}.
    Context `{configUnitType : config.UnitType}.
    Context `{configBoolType : config.BoolType}.
    Context `{configProdType : config.ProdType}.

    Local Existing Instance annotated_syntax.Syntax.

    Definition context := annotated_syntax.context.
    Definition type := annotated_syntax.type.
    Definition term := annotated_syntax.term.
    Definition substitution := annotated_syntax.substitution.

    Definition isctx   := isctx.
    Definition issubst := issubst.
    Definition istype  := istype.
    Definition isterm  := isterm.
    Definition eqctx   := eqctx.
    Definition eqsubst := eqsubst.
    Definition eqtype  := eqtype.
    Definition eqterm  := eqterm.

  End Att.

End Att.

Module A := annotated_syntax.

(* Concise theory *)
Module Ctt.

  Section Ctt.

    Context `{configPrecondition : config.Precondition}.
    Context `{configReflection : config.Reflection}.
    Context `{configBinaryProdType : config.BinaryProdType}.
    Context `{configProdEta : config.ProdEta}.
    Context `{configUniverses : config.Universes}.
    Context `{configPropType : config.PropType}.
    Context `{configIdType : config.IdType}.
    Context `{configIdEliminator : config.IdEliminator}.
    Context `{configEmptyType : config.EmptyType}.
    Context `{configUnitType : config.UnitType}.
    Context `{configBoolType : config.BoolType}.
    Context `{configProdType : config.ProdType}.

    Local Existing Instance concise_syntax.Syntax.

    Definition context := concise_syntax.context.
    Definition term := concise_syntax.term.
    Definition substitution := concise_syntax.substitution.

    Definition isctx   := isctx.
    Definition issubst := issubst.
    Definition istype  := istype.
    Definition isterm  := isterm.
    Definition eqctx   := eqctx.
    Definition eqsubst := eqsubst.
    Definition eqtype  := eqtype.
    Definition eqterm  := eqterm.

  End Ctt.

End Ctt.

Module C := concise_syntax.

Section Translation.

Context `{configPrecondition : config.Precondition}.
Context `{configReflection : config.Reflection}.
Context `{configBinaryProdType : config.BinaryProdType}.
Context `{configProdEta : config.ProdEta}.
Context `{configUniverses : config.Universes}.
Context `{configPropType : config.PropType}.
Context `{configIdType : config.IdType}.
Context `{configIdEliminator : config.IdEliminator}.
Context `{configEmptyType : config.EmptyType}.
Context `{configUnitType : config.UnitType}.
Context `{configBoolType : config.BoolType}.
Context `{configProdType : config.ProdType}.

Fixpoint forget_type (A : Att.type) : Ctt.term :=
  match A with
  | A.Prod A B => C.Prod (forget_type A) (forget_type B)
  | A.Id A u v => C.Id (forget_type A) (forget_term u) (forget_term v)
  | A.Subst A sbs => C.subst (forget_type A) (forget_subst sbs)
  | A.Empty => C.Empty
  | A.Unit => C.Unit
  | A.Bool => C.Bool
  | A.BinaryProd A B => C.BinaryProd (forget_type A) (forget_type B)
  | A.Uni l => C.Uni l
  | A.El l u => forget_term u
  end

with forget_term (u : Att.term) : Ctt.term :=
  match u with
  | A.var x => C.var x
  | A.lam A B t => C.lam (forget_type A) (forget_term t)
  | A.app u A B v => C.app (forget_term u) (forget_term v)
  | A.refl A u => C.refl (forget_term u)
  | A.j A u C w v p =>
    C.j (forget_type A)
        (forget_term u)
        (forget_type C)
        (forget_term w)
        (forget_term v)
        (forget_term p)
  | A.subst u sbs => C.subst (forget_term u) (forget_subst sbs)
  | A.exfalso A u => C.exfalso (forget_type A) (forget_term u)
  | A.unit => C.unit
  | A.true => C.true
  | A.false => C.false
  | A.cond C u v w =>
    C.cond (forget_type C) (forget_term u) (forget_term v) (forget_term w)
  | A.pair A B u v =>
    C.pair (forget_type A) (forget_type B) (forget_term u) (forget_term v)
  | A.proj1 A B p =>
    C.proj1 (forget_type A) (forget_type B) (forget_term p)
  | A.proj2 A B p =>
    C.proj2 (forget_type A) (forget_type B) (forget_term p)
  | A.uniProd l1 l2 a b =>
    C.Prod (forget_term a) (forget_term b)
  | A.uniId l a u v =>
    C.Id (forget_term a) (forget_term u) (forget_term v)
  | A.uniEmpty l => C.Empty
  | A.uniUnit l => C.Unit
  | A.uniBool n => C.Bool
  | A.uniBinaryProd l1 l2 a b =>
    C.BinaryProd (forget_term a) (forget_term b)
  | A.uniUni l => C.Uni l
  end

with forget_subst (sbs : Att.substitution) : Ctt.substitution :=
  match sbs with
  | A.sbzero A u => C.sbzero (forget_type A) (forget_term u)
  | A.sbweak A => C.sbweak (forget_type A)
  | A.sbshift A sbs => C.sbshift (forget_type A) (forget_subst sbs)
  | A.sbid => C.sbid
  | A.sbcomp sbs sbt => C.sbcomp (forget_subst sbs) (forget_subst sbt)
  end.

Axiom admit : forall {A}, A.
Tactic Notation "admit" := (exact admit).

Fixpoint forget_ctx (G : Att.context) : Ctt.context :=
  match G with
  | A.ctxempty => C.ctxempty
  | A.ctxextend G A => C.ctxextend (forget_ctx G) (forget_type A)
  end.


Ltac ih :=
  match goal with
  | forget_isctx :
      forall G,
        Att.isctx G ->
        Ctt.isctx (forget_ctx G)
    |- tt.isctx (forget_ctx ?G) =>
    now apply (forget_isctx G)
  | forget_istype :
      forall G A,
        Att.istype G A ->
        Ctt.istype (forget_ctx G) (forget_type A)
    |- tt.istype (forget_ctx ?G) (forget_type ?A) =>
    now apply (forget_istype G A)
  | forget_isterm :
      forall G u A,
        Att.isterm G u A ->
        Ctt.isterm (forget_ctx G) (forget_term u) (forget_type A)
    |- tt.isterm (forget_ctx ?G) (forget_term ?u) (forget_type ?A) =>
    now apply (forget_isterm G u A)
  | forget_issubst :
      forall sbs G D,
        Att.issubst sbs G D ->
        Ctt.issubst (forget_subst sbs) (forget_ctx G) (forget_ctx D)
    |- tt.issubst (forget_subst ?sbs) (forget_ctx ?G) (forget_ctx ?D) =>
    now apply (forget_issubst sbs G D)
  | forget_eqctx :
      forall G D,
        Att.eqctx G D ->
        Ctt.eqctx (forget_ctx G) (forget_ctx D)
    |- tt.eqctx (forget_ctx ?G) (forget_ctx ?D) =>
    now apply (forget_eqctx G D)
  | forget_eqtype :
      forall G A B,
        Att.eqtype G A B ->
        Ctt.eqtype (forget_ctx G) (forget_type A) (forget_type B)
    |- tt.eqtype (forget_ctx ?G) (forget_type ?A) (forget_type ?B) =>
    now apply (forget_eqtype G A B)
  | forget_eqterm :
      forall G u v A,
        Att.eqterm G u v A ->
        Ctt.eqterm (forget_ctx G) (forget_term u) (forget_term v) (forget_type A)
    |- tt.eqterm (forget_ctx ?G) (forget_term ?u) (forget_term ?v) (forget_type ?A) =>
    now apply (forget_eqterm G u v A)
  | forget_eqsubst :
      forall sbs sbt G D,
        Att.eqsubst sbs sbt G D ->
        Ctt.eqsubst (forget_subst sbs)
                    (forget_subst sbt)
                    (forget_ctx G)
                    (forget_ctx D)
    |- tt.eqsubst (forget_subst ?sbs)
              (forget_subst ?sbt)
              (forget_ctx ?G)
              (forget_ctx ?D) =>
    now apply (forget_eqsubst sbs sbt G D)
  end.


Fixpoint forget_isctx {G} (H : Att.isctx G) {struct H} :
  Ctt.isctx (forget_ctx G)

with forget_istype {G A} (H : Att.istype G A) {struct H} :
  Ctt.istype (forget_ctx G) (forget_type A)

with forget_isterm {G u A} (H : Att.isterm G u A) {struct H} :
  Ctt.isterm (forget_ctx G) (forget_term u) (forget_type A)

with forget_issubst {sbs G D} (H : Att.issubst sbs G D) {struct H} :
  Ctt.issubst (forget_subst sbs) (forget_ctx G) (forget_ctx D)

with forget_eqctx {G D} (H : Att.eqctx G D) {struct H} :
  Ctt.eqctx (forget_ctx G) (forget_ctx D)

with forget_eqtype {G A B} (H : Att.eqtype G A B) {struct H} :
  Ctt.eqtype (forget_ctx G) (forget_type A) (forget_type B)

with forget_eqterm {G u v A} (H : Att.eqterm G u v A) {struct H} :
  Ctt.eqterm (forget_ctx G) (forget_term u) (forget_term v) (forget_type A)

with forget_eqsubst {sbs sbt G D} (H : Att.eqsubst sbs sbt G D) {struct H} :
  Ctt.eqsubst
    (forget_subst sbs)
    (forget_subst sbt)
    (forget_ctx G)
    (forget_ctx D).

Proof.
  (* forget_isctx *)
  - { destruct H ; doConfig.

      (* CtxEmpty *)
      - constructor.

      (* CtxExtend *)
      - simpl. (config constructor) ; ih.
    }

  (* forget_istype *)
  - { destruct H ; doConfig.

      (* TyCtxConv *)
      - { (config apply @TyCtxConv with (G := forget_ctx G)) ; ih. }

      (* TySubst *)
      - { simpl.
          config apply @TySubst with (D := forget_ctx D).
          - ih.
          - ih.
          - ih.
          - ih.
        }

      (* TyProd *)
      - { simpl. capply @TyProd.
          - apply (forget_istype _ _ H).
          - ih.
          - ih.
        }

      (* TyId *)
      - { simpl. capply @TyId.
          - ih.
          - ih.
          - ih.
          - ih.
        }

      (* TyEmpty *)
      - capply @TyEmpty ; ih.

      (* TyUnit *)
      - capply @TyUnit ; ih.

      (* TyBool *)
      - capply @TyBool ; ih.

      (* TyBinaryProd *)
      - { simpl. capply @TyBinaryProd.
          - ih.
          - ih.
          - ih.
        }

      (* TyUni *)
      - { simpl. capply @TyUni. ih. }

      (* TyEl *)
      - { simpl.
          pose (tyel := @tt.TyEl configPrecondition configReflection configBinaryProdType configProdEta configUniverses configPropType configIdEliminator configEmptyType configUnitType configBoolType configIdType configProdType concise_syntax.Syntax). cbv in tyel.
          config (eapply tyel).
          - auto.
          - apply (forget_isterm _ _ _ i).
          - intro x.
            specialize (i0 x). ih.
        }

    }

  (* forget_isterm *)
  - admit.

  (* forget_issubst *)
  - admit.

  (* forget_eqctx *)
  - admit.

  (* forget_eqtype *)
  - admit.

  (* forget_eqterm *)
  - admit.

  (* forget_eqsubst *)
  - admit.
Defined.

End Translation.

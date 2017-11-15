(* Elaborating Annotations

   We propose a translation from concise syntax to annotated syntax.
   For this purpose, we have to rely on a typing derivation to retrieve
   the missing annotations.
 *)

Require config.
Require Import config_tactics.

Require syntax.
Require Import tt.
Require annotated_syntax concise_syntax.
Require Import forget_annotation.

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

Open Scope type_scope.

(* Notion of elaborations *)
Record context_elab (G : C.context) := {
  ctx : A.context ;
  eqctx : forget_ctx ctx = G ;
  isctx : Att.isctx ctx
}.

Arguments ctx {_} _.
Arguments eqctx {_} _.
Arguments isctx {_} _.

Record type_elab {G} A (Ge : context_elab G) := {
  ty : A.type ;
  eqty : forget_type ty = A ;
  isty : Att.istype (ctx Ge) ty
}.

Arguments ty {_ _ _} _.
Arguments eqty {_ _ _} _.
Arguments isty {_ _ _} _.

Record term_elab {G A} u {Ge : context_elab G} (Ae : type_elab A Ge) := {
  tm : A.term ;
  eqtm : forget_term tm = u ;
  istm : Att.isterm (ctx Ge) tm (ty Ae)
}.

Arguments tm {_ _ _ _ _} _.
Arguments eqtm {_ _ _ _ _} _.
Arguments istm {_ _ _ _ _} _.

Record subst_elab {G D} sbs (Ge : context_elab G) (De : context_elab D) := {
  sb : A.substitution ;
  eqsb : forget_subst sb = sbs ;
  issb : Att.issubst sb (ctx Ge) (ctx De)
}.

Arguments sb {_ _ _ _ _} _.
Arguments eqsb {_ _ _ _ _} _.
Arguments issb {_ _ _ _ _} _.

Axiom admit : forall {A}, A.
Tactic Notation "admit" := (exact admit).

Fixpoint elab_ctx G (H : Ctt.isctx G) {struct H} :
  context_elab G

with elab_type G A (H : Ctt.istype G A) (Ge : context_elab G) {struct H} :
  type_elab A Ge

with elab_term G A u (H : Ctt.isterm G u A)
               (Ge : context_elab G) (Ae : type_elab A Ge) {struct H} :
  term_elab u Ae

with elab_subst G D sbs (H : Ctt.issubst sbs G D)
                (Ge : context_elab G) (De : context_elab D) {struct H} :
  subst_elab sbs Ge De.

Proof.

  (* elab_ctx *)
  - admit.

  (* elab_type *)
  - admit.

  (* elab_term *)
  - admit.

  (* elab_subst *)
  - admit.

Defined.

Close Scope type_scope.

End Translation.
(* We attempt a formalisation that goes from reflection for dSet to
   definitional UIP dSet.
*)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require Import checking_tactics.

(* Source type theory *)
Module Stt.

  Section Stt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.Yes |}.
  Local Instance hasReflection : config.Reflection
    := {| config.reflectionFlag := config.No |}.
  Local Instance hasSimpleProducts : config.SimpleProducts
    := {| config.simpleproductsFlag := config.No |}.
  Local Instance hasProdEta : config.ProdEta
    := {| config.prodetaFlag := config.No |}.
  Local Instance hasUniverses : config.Universes
    := {| config.universesFlag := config.No |}.
  Local Instance hasProp : config.WithProp
    := {| config.withpropFlag := config.No |}.
  Local Instance hasJ : config.WithJ
    := {| config.withjFlag := config.No |}.
  Local Instance hasEmpty : config.WithEmpty
    := {| config.withemptyFlag := config.No |}.
  Local Instance hasUnit : config.WithUnit
    := {| config.withunitFlag := config.No |}.
  Local Instance hasBool : config.WithBool
    := {| config.withboolFlag := config.No |}.
  Context `{isdset : context -> type -> config.Dec}.
  Local Instance hasDSetReflection : config.DSetReflection
    := {| config.dsetreflectionFlag := config.Yes ;
         config.dsetreflectionCriterion := isdset |}.
  Local Instance hasDSetUIP : config.DSetUIP
    := {| config.dsetuipFlag := config.No ;
         config.dsetuipCriterion G A := config.ko |}.

  Definition isctx   := isctx.
  Definition issubst := issubst.
  Definition istype  := istype.
  Definition isterm  := isterm.
  Definition eqctx   := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype  := eqtype.
  Definition eqterm  := eqterm.

  End Stt.

End Stt.

(* Target type theory *)
Module Ttt.

  Section Ttt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.No |}.
  Local Instance hasReflection : config.Reflection
    := {| config.reflectionFlag := config.No |}.
  Local Instance hasSimpleProducts : config.SimpleProducts
    := {| config.simpleproductsFlag := config.No |}.
  Local Instance hasProdEta : config.ProdEta
    := {| config.prodetaFlag := config.No |}.
  Local Instance hasUniverses : config.Universes
    := {| config.universesFlag := config.No |}.
  Local Instance hasProp : config.WithProp
    := {| config.withpropFlag := config.No |}.
  Local Instance hasJ : config.WithJ
    := {| config.withjFlag := config.No |}.
  Local Instance hasEmpty : config.WithEmpty
    := {| config.withemptyFlag := config.No |}.
  Local Instance hasUnit : config.WithUnit
    := {| config.withunitFlag := config.No |}.
  Local Instance hasBool : config.WithBool
    := {| config.withboolFlag := config.No |}.
  Context `{isdset : context -> type -> config.Dec}.
  Local Instance hasDSetReflection : config.DSetReflection
    := {| config.dsetreflectionFlag := config.No ;
         config.dsetreflectionCriterion G A := config.ko |}.
  Local Instance hasDSetUIP : config.DSetUIP
    := {| config.dsetuipFlag := config.No ;
         config.dsetuipCriterion := isdset |}.

  Definition isctx   := isctx.
  Definition issubst := issubst.
  Definition istype  := istype.
  Definition isterm  := isterm.
  Definition eqctx   := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype  := eqtype.
  Definition eqterm  := eqterm.

  End Ttt.

End Ttt.

Section Translation.

Context `{isdset : context -> type -> config.Dec}.

End Translation.

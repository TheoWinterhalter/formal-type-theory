(* In order to test our formalisation, we propose our own formalisation of a
   model that negates function extensionality, following Simon Boulier,
   Pierre-Marie Pédrot et Nicolas Tabareau.
*)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.

(* Source type theory *)
Module Stt.

  Section Stt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.Yes |}.
  Context `{configReflection : config.Reflection}.

  Definition isctx := isctx.
  Definition issubst := issubst.
  Definition istype := istype.
  Definition isterm := isterm.
  Definition eqctx := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype := eqtype.
  Definition eqterm := eqterm.

  End Stt.

End Stt.

(* Target type theory *)
Module Ttt.

  Section Ttt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.No |}.
  Context `{configReflection : config.Reflection}.

  Definition isctx := isctx.
  Definition issubst := issubst.
  Definition istype := istype.
  Definition isterm := isterm.
  Definition eqctx := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype := eqtype.
  Definition eqterm := eqterm.

  End Ttt.

End Ttt.

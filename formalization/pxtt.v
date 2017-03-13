(* The source type theory, paranoid extensional type theory *)

Require config.
Require Import tt.

Section Pxtt.

Local Instance hasPrecond : config.Precond
  := {| config.precondFlag := config.Yes |}.
Local Instance hasReflection : config.Reflection
  := {| config.reflectionFlag := config.Yes |}.

Definition isctx := isctx.
Definition issubst := issubst.
Definition istype := istype.
Definition isterm := isterm.
Definition eqctx := eqctx.
Definition eqsubst := eqsubst.
Definition eqtype := eqtype.
Definition eqterm := eqterm.

End Pxtt.

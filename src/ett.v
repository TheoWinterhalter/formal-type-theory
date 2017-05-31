Require config.
Require Import tt.

Section Ett.

Local Instance hasPrecond : config.Precond := {| config.precondFlag := config.No |}.
Context {ConfigSyntax : config.Syntax}.
Context {ConfigReflection : config.Reflection}.
Context {ConfigSimpleProducts : config.SimpleProducts}.
Context {ConfigProdEta : config.ProdEta}.
Context {ConfigUniverseLevels : config.UniverseLevels}.
Context {ConfigUniverses : config.Universes}.
Context {ConfigWithProp : config.WithProp}.
Context {ConfigWithJ : config.WithJ}.
Context {ConfigEmpty : config.WithEmpty}.
Context {ConfigUnit : config.WithUnit}.
Context {ConfigBool : config.WithBool}.
Context {ConfigPi : config.WithPi}.
Context {ConfigUniProd : config.UniProd}.
Context {ConfigUniId : config.UniId}.
Context {ConfigUniEmpty : config.UniEmpty}.
Context {ConfigUniUnit : config.UniUnit}.
Context {ConfigUniBool : config.UniBool}.
Context {ConfigUniSimProd : config.UniSimProd}.

Definition isctx := isctx.
Definition issubst := issubst.
Definition istype := istype.
Definition isterm := isterm.
Definition eqctx := eqctx.
Definition eqsubst := eqsubst.
Definition eqtype := eqtype.
Definition eqterm := eqterm.

End Ett.
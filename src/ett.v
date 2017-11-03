Require config.
Require tt.
Require syntax.

Section Ett.

Local Instance hasPrecond : config.Precond := {| config.precondFlag := config.No |}.
Context `{configReflection : config.Reflection}.
Context `{configSimpleProducts : config.SimpleProducts}.
Context `{ConfigProdEta : config.ProdEta}.
Context `{ConfigUniverses : config.Universes}.
Context `{ConfigWithProp : config.WithProp}.
Context `{ConfigId : config.IdentityTypes}.
Context `{ConfigWithJ : config.WithJ}.
Context `{ConfigEmpty : config.WithEmpty}.
Context `{ConfigUnit : config.WithUnit}.
Context `{ConfigBool : config.WithBool}.
Context `{ConfigPi : config.WithPi}.
Context `{haveSyntax : syntax.Syntax}.

Definition isctx := tt.isctx.
Definition issubst := tt.issubst.
Definition istype := tt.istype.
Definition isterm := tt.isterm.
Definition eqctx := tt.eqctx.
Definition eqsubst := tt.eqsubst.
Definition eqtype := tt.eqtype.
Definition eqterm := tt.eqterm.

End Ett.
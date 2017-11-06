Require config.
Require tt.
Require syntax.

Section Ptt.

Local Instance hasPrecond : config.Precond := {| config.precondFlag := config.Yes |}.
Context `{configReflection : config.Reflection}.
Context `{configSimpleProducts : config.SimpleProducts}.
Context `{configProdEta : config.ProdEta}.
Context `{configUniverses : config.Universes}.
Context `{configWithProp : config.WithProp}.
Context `{configId : config.IdentityTypes}.
Context `{configWithJ : config.WithJ}.
Context `{configEmpty : config.WithEmpty}.
Context `{configUnit : config.WithUnit}.
Context `{configBool : config.WithBool}.
Context `{configPi : config.WithPi}.
Context `{configSyntax : syntax.Syntax}.

Definition isctx := tt.isctx.
Definition issubst := tt.issubst.
Definition istype := tt.istype.
Definition isterm := tt.isterm.
Definition eqctx := tt.eqctx.
Definition eqsubst := tt.eqsubst.
Definition eqtype := tt.eqtype.
Definition eqterm := tt.eqterm.

End Ptt.

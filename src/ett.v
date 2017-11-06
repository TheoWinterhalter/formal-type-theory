Require config.
Require tt.
Require syntax.

Section Ett.

Local Instance hasPrecondition : config.Precondition := {| config.flagPrecondition := config.No |}.
Context `{configReflection : config.Reflection}.
Context `{configBinaryProdType : config.BinaryProdType}.
Context `{configProdEta : config.ProdEta}.
Context `{configUniverses : config.Universes}.
Context `{configWithProp : config.WithProp}.
Context `{configIdType : config.IdType}.
Context `{configIdEliminator : config.IdEliminator}.
Context `{configEmpty : config.WithEmpty}.
Context `{configUnit : config.WithUnit}.
Context `{configBool : config.WithBool}.
Context `{configProdType : config.ProdType}.
Context `{configSyntax : syntax.Syntax}.

Definition isctx := tt.isctx.
Definition issubst := tt.issubst.
Definition istype := tt.istype.
Definition isterm := tt.isterm.
Definition eqctx := tt.eqctx.
Definition eqsubst := tt.eqsubst.
Definition eqtype := tt.eqtype.
Definition eqterm := tt.eqterm.

End Ett.
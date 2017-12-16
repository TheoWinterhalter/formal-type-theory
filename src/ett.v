Require config.
Require tt.
Require syntax.

Section Ett.

Local Instance havePrecondition : config.Precondition := {| config.flagPrecondition := config.No |}.
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
Context `{configSyntax : syntax.Syntax}.

Definition isctx := tt.isctx.
Definition istype := tt.istype.
Definition isterm := tt.isterm.
Definition eqctx := tt.eqctx.
Definition eqtype := tt.eqtype.
Definition eqterm := tt.eqterm.

End Ett.
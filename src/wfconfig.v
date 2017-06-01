Require Import config.
Require Import tt.

Section WellFormedConfiguration.

Context {ConfigSyntax : config.Syntax}.
Context {ConfigPrecond : config.Precond}.
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

Class CtxExtendInversionClass := {
  CtxExtendInversion : forall G A,
                         isctx (ctxextend G A) ->
                         isctx G * istype G A
}.

Class TyIdInversionClass := {
  TyIdInversion : forall G A u v,
                    istype G (Id A u v) ->
                    isctx G * istype G A * isterm G u A * isterm G v A
}.

Class TyProdInversionClass := {
  TyProdInversion : forall `{_ : Flag withpiFlag} G A B,
                      istype G (Prod A B) ->
                      isctx G * istype G A * istype (ctxextend G A) B
}.

Class TySimProdInversionClass := {
  TySimProdInversion : forall `{_ : Flag simpleproductsFlag} G A B,
                         istype G (SimProd A B) ->
                         isctx G * istype G A * istype G B
}.

End WellFormedConfiguration.

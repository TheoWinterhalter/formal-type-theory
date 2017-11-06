(* Inversion principles as configurations *)

Require Import config syntax tt.

Section InversionPrinciples.

Context `{configPrecond : config.Precond}.
Context `{configReflection : config.Reflection}.
Context `{configSimpleProducts : config.SimpleProducts}.
Context `{configProdEta : config.ProdEta}.
Context `{ConfigUniverses : config.Universes}.
Context `{ConfigWithProp : config.WithProp}.
Context `{ConfigId : config.IdentityTypes}.
Context `{ConfigWithJ : config.WithJ}.
Context `{ConfigEmpty : config.WithEmpty}.
Context `{ConfigUnit : config.WithUnit}.
Context `{ConfigBool : config.WithBool}.
Context `{ConfigPi : config.WithPi}.

Context `{haveSyntax : syntax.Syntax}.

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
  TyProdInversion : forall G A B,
                      istype G (Prod A B) ->
                      isctx G * istype G A * istype (ctxextend G A) B
}.

Class TySimProdInversionClass := {
  TySimProdInversion : forall G A B,
                         istype G (SimProd A B) ->
                         isctx G * istype G A * istype G B
}.

Class EqCtxExtendInversionClass := {
  EqCtxExtendInversion : forall G A G' A',
                           eqctx (ctxextend G A) (ctxextend G' A') ->
                           eqctx G G' * eqtype G A A'
}.

End InversionPrinciples.

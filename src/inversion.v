(* Statement of inversion principles. *)

Require Import config syntax tt.

Section InversionPrinciples.

Context `{configPrecondition : config.Precondition}.
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

Class HaveCtxExtendInversion := {
  CtxExtendInversion : forall G A,
                         isctx (ctxextend G A) ->
                         isctx G * istype G A
}.

Class HaveTyIdInversion := {
  TyIdInversion : forall G A u v,
                    istype G (Id A u v) ->
                    isctx G * istype G A * isterm G u A * isterm G v A
}.

Class HaveTyProdInversion := {
  TyProdInversion : forall G A B,
                      istype G (Prod A B) ->
                      isctx G * istype G A * istype (ctxextend G A) B
}.

Class HaveTyBinaryProdInversion := {
  TyBinaryProdInversion : forall G A B,
                         istype G (BinaryProd A B) ->
                         isctx G * istype G A * istype G B
}.

Class HaveEqCtxExtendInversion := {
  EqCtxExtendInversion : forall G A G' A',
                           eqctx (ctxextend G A) (ctxextend G' A') ->
                           eqctx G G' * eqtype G A A'
}.

End InversionPrinciples.

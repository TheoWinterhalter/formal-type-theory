Require syntax.

Inductive Yes : Type := yes.
Inductive No : Type := .
Inductive Dec : Type := ok | ko.

Class Precond := {
  precondFlag : Type
}.

Class Reflection := {
  reflectionFlag : Type
}.

Class SimpleProducts := {
  simpleproductsFlag : Type
}.

Class ProdEta := {
  prodetaFlag : Type
}.

Class Universes := {
  universesFlag : Type
}.

Class WithProp := {
  withpropFlag : Type
}.

Class WithJ := {
  withjFlag : Type
}.

Class WithEmpty := {
  withemptyFlag : Type
}.

Class WithUnit := {
  withunitFlag : Type
}.

Class WithBool := {
  withboolFlag : Type
}.

Class DSetReflection := {
  dsetreflectionFlag : Type ;
  dsetreflectionCriterion : syntax.context -> syntax.type -> Dec
}.

Class DSetUIP := {
  dsetuipFlag : Type ;
  dsetuipCriterion : syntax.context -> syntax.type -> Dec
}.

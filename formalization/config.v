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

(* TODO: Class for Prop, or maybe even allow only one universe? *)

Inductive Yes : Type := yes.
Inductive No : Type := .

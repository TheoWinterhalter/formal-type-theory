(* Definitions of configuration options. *)

(* Use these types to instantiate the configuration type classes below. *)

Inductive Yes : Type := yes.
Inductive No : Type := .

(* Each configurable feature is represented by a type class which contains a
   type.

   To turn on a configuration, provide a type class instance in which the type
   is instantiated to `Yes`.

   To turn off a configuration, provide a type class instance in which the type
   is instantiated to `No`.

   To be ambivalent about a configuration, provide a `Context` with an
   unspecified instance of it. Then your development will be parametrized by it
   automagically.

   You have to make sure that you do not provid *two* instances for the same
   configuration option. The best way to do this is to always make sure that all
   the instances are declatered as [Local].
*)

(* Paranoid mode, include preconditions in rules. *)
Class Precondition := {
  flagPrecondition : Type
}.

(* Dependent products. *)
Class ProdType := {
  flagProdType : Type
}.

(* The eta-rule for functions. *)
Class ProdEta := {
  flagProdEta : Type
}.

(* Identity types. *)
Class IdType := {
  flagIdType : Type
}.

(* J-eliminator. *)
Class IdEliminator := {
  flagIdEliminator : Type
}.

(* Equality reflection. *)
Class Reflection := {
  flagReflection : Type
}.

(* Binary products. *)
Class BinaryProdType := {
  flagBinaryProdType : Type
}.

(* Dependent sums. *)
Class SumType := {
  flagSumType : Type
}.

(* Universes *)
Class Universes := {
  flagUniverses : Type
}.

(* Impredicative universe of propositions. *)
Class PropType := {
  flagPropType : Type
}.

(* Empty type. *)
Class EmptyType := {
  flagEmptyType : Type
}.

(* Unit type. *)
Class UnitType := {
  flagUnitType : Type
}.

(* Boolean type. *)
Class BoolType := {
  flagBoolType : Type
}.

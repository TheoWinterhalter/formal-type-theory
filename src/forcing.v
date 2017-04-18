(* Forcing Translation

   Based on The Definitional Side of the Forcing
   by Jaber et al.
*)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require Import checking_tactics.

(* Source type theory *)
Module Stt.

  Section Stt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.Yes |}.
  Local Instance hasReflection : config.Reflection
    := {| config.reflectionFlag := config.No |}.
  Local Instance hasSimpleProducts : config.SimpleProducts
    := {| config.simpleproductsFlag := config.No |}.
  Local Instance hasProdEta : config.ProdEta
    := {| config.prodetaFlag := config.No |}.
  Local Instance hasUniverses : config.Universes
    := {| config.universesFlag := config.Yes |}.
  Local Instance hasProp : config.WithProp
    := {| config.withpropFlag := config.Yes |}.

  Definition isctx   := isctx.
  Definition issubst := issubst.
  Definition istype  := istype.
  Definition isterm  := isterm.
  Definition eqctx   := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype  := eqtype.
  Definition eqterm  := eqterm.

  End Stt.

End Stt.

(* Target type theory *)
Module Ttt.

  Section Ttt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.No |}.
  Local Instance hasReflection : config.Reflection
    := {| config.reflectionFlag := config.No |}.
  Local Instance hasSimpleProducts : config.SimpleProducts
    := {| config.simpleproductsFlag := config.No |}.
  Local Instance hasProdEta : config.ProdEta
    := {| config.prodetaFlag := config.No |}.
  Local Instance hasUniverses : config.Universes
    := {| config.universesFlag := config.Yes |}.
  Local Instance hasProp : config.WithProp
    := {| config.withpropFlag := config.Yes |}.

  Definition isctx   := isctx.
  Definition issubst := issubst.
  Definition istype  := istype.
  Definition isterm  := isterm.
  Definition eqctx   := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype  := eqtype.
  Definition eqterm  := eqterm.

  End Ttt.

End Ttt.

Section Translation.

(* We give ourselves a category in the source *)
(* Note: This should also hold in the target by equivalence ett/ptt. *)
Context `{ℙ : term}.
Context `{hℙ : Stt.isterm ctxempty ℙ (Uni (uni 0))}.
Context `{Hom : term}.
Context `{hHom : Stt.isterm ctxempty Hom (Arrow (El ℙ) (Arrow (El ℙ) (Uni (uni 0))))}.
Context `{idℙ : term}.
Context `{hidℙ : Stt.isterm ctxempty idℙ (Prod (El ℙ) (El (app (app Hom (El ℙ) (Arrow (El ℙ) (Uni (uni 0))) (var 0)) (El ℙ) (Uni (uni 0)) (var 0))))}.
Context `{comp : term}.
Context `{hcomp : Stt.isterm ctxempty comp (Prod (El ℙ) (Prod (El ℙ) (Prod (El ℙ) (Arrow (El (app (app Hom (El ℙ) (Arrow (El ℙ) (Uni (uni 0))) (var 2)) (El ℙ) (Uni (uni 0)) (var 1))) (Arrow (El (app (app Hom (El ℙ) (Arrow (El ℙ) (Uni (uni 0))) (var 1)) (El ℙ) (Uni (uni 0)) (var 0))) (El (app (app Hom (El ℙ) (Arrow (El ℙ) (Uni (uni 0))) (var 2)) (El ℙ) (Uni (uni 0)) (var 0))))))))}.

(* This is really illegible so we need to complete the alternative syntax. *)

End Translation.
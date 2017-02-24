Require Import tt.

Module Make
       (ConfigPrecond : CONFIG_PRECOND)
       (ConfigReflection : CONFIG_REFLECTION).

(* Deal with configuration. *)
Ltac doConfig :=
  (* configure the goal *)
  match goal with

  (* Simplify the goal wrt preconditions *)
  | |- (HasPrecond.precondFlag -> _) =>
    (intros _)
  | |- (HasntPrecond.precondFlag -> _) =>
    let H := fresh "Eco" in
    (intros H ; now elim H)
  | |- (ConfigPrecond.precondFlag -> _) =>
    let H := fresh "hasPrecond" in
    (intros H)

  (* Simplify the goal wrt reflection *)
  | |- (HasReflection.reflectionFlag -> _) =>
    (intros _)
  | |- (HasntReflection.reflectionFlag -> _) =>
    let H := fresh "Ref" in
    (intros H ; now elim H)
  | |- (ConfigReflection.reflectionFlag -> _) =>
    let H := fresh "hasReflection" in
    (intros H)
  | _ => idtac
  end ;

  (* Configure the hypotheses *)
  repeat
  (match goal with

   | H : HasPrecond.precondFlag -> ?A |- _ =>
     apply (fun (f : HasPrecond.precondFlag -> A) => f HasPrecond.precond) in H
   | H : HasntPrecond.precondFlag -> _ |- _ =>
     clear H
   | H : ConfigPrecond.precondFlag -> ?A, R : ConfigPrecond.precondFlag |- _ =>
     apply (fun (f : ConfigPrecond.precondFlag -> A) => f R) in H

   | H : HasReflection.reflectionFlag -> ?A |- _ =>
     apply (fun (f : HasReflection.reflectionFlag -> A) => f HasReflection.reflection) in H
   | H : HasntReflection.reflectionFlag -> _ |- _ =>
     clear H
   | H : ConfigReflection.reflectionFlag -> ?A, R : ConfigReflection.reflectionFlag |- _ =>
     apply (fun (f : ConfigReflection.reflectionFlag -> A) => f R) in H
   end).

(* Perform a tactic and deal with a configuration. *)
Tactic Notation (at level 0) "config" tactic(t) := doConfig ; t ; doConfig.

Tactic Notation (at level 5) "capply" uconstr(H) := doConfig ; apply H ; doConfig.

Tactic Notation (at level 5) "ceapply" uconstr(H) := doConfig ; eapply H ; doConfig.

End Make.
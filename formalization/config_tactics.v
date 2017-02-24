Require Import tt.

(* Deal with configuration. *)
Ltac doConfig :=
  (* configure the hypotheses *)
  repeat
  (match goal with
   | H : ParanoidConfiguration.Paranoia -> ?A |- _ =>
     apply (fun (f : ParanoidConfiguration.Paranoia -> A) => f ParanoidConfiguration.paranoia) in H
   | H : EconomicConfiguration.Paranoia -> _ |- _ =>
     clear H
   end) ;
  (* configure the goal *)
  match goal with
  | |- (ParanoidConfiguration.Paranoia -> _) =>
    (intros _)
  | |- (EconomicConfiguration.Paranoia -> _) =>
    let H := fresh "Eco" in
    (intros H ; now elim H)
  | _ => idtac
  end.

(* Perform a tactic and deal with a configuration. *)
Tactic Notation (at level 0) "config" tactic(t) := doConfig ; t ; doConfig.

Tactic Notation (at level 5) "capply" uconstr(H) := doConfig ; apply H ; doConfig.

Tactic Notation (at level 5) "ceapply" uconstr(H) := doConfig ; eapply H ; doConfig.


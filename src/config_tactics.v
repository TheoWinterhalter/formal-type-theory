Require Import config.

(* Deal with configuration. *)
Ltac doConfig :=
  (* configure the goal *)
  match goal with
  | |- ?P -> ?Q =>
    match (eval cbn in P) with
    | Yes => intros _
    | No => let H := fresh "H" in (intros H ; now elim H)
    | preconditionFlag =>
      let H := fresh "preconditionFlag" in intros H
    | reflectionFlag =>
      let H := fresh "reflectionFlag" in intros H
    | binaryProdTypeFlag =>
      let H := fresh "binaryProdTypeFlag" in intros H
    | prodetaFlag =>
      let H := fresh "prodetaFlag" in intros H
    | universesFlag =>
      let H := fresh "universesFlag" in intros H
    | withpropFlag =>
      let H := fresh "withpropFlag" in intros H
    | withjFlag =>
      let H := fresh "withjFlag" in intros H
    | withemptyFlag =>
      let H := fresh "withemptyFlag" in intros H
    | withunitFlag =>
      let H := fresh "withunitFlag" in intros H
    | withboolFlag =>
      let H := fresh "withboolFlag" in intros H
    | prodTypeFlag =>
      let H := fresh "prodTypeFlag" in intros H
    | identitytypesFlag =>
      let H := fresh "identitytypesFlag" in intros H
    | _ => idtac
    end
  | |- ?P =>
    match (eval cbn in P) with
    | Yes => exact yes
    end
  | H : preconditionFlag |- preconditionFlag => exact H
  | H : reflectionFlag |- reflectionFlag => exact H
  | H : binaryProdTypeFlag |- binaryProdTypeFlag => exact H
  | H : prodetaFlag |- prodetaFlag => exact H
  | H : universesFlag |- universesFlag => exact H
  | H : withpropFlag |- withpropFlag => exact H
  | H : withjFlag |- withjFlag => exact H
  | H : withemptyFlag |- withemptyFlag => exact H
  | H : withunitFlag |- withunitFlag => exact H
  | H : withboolFlag |- withboolFlag => exact H
  | H : prodTypeFlag |- prodTypeFlag => exact H
  | H : identitytypesFlag |- identitytypesFlag => exact H
  | _ => idtac
  end ;
  (* Configure the hypotheses *)
  repeat
  (match goal with
   | H : ?P -> ?Q |- _ =>
     match (eval cbn in P) with
     | Yes => specialize (H yes)
     | No => clear H
     | @preconditionFlag ?F =>
       match goal with
       | R : @preconditionFlag F |- _ => specialize (H R)
       end
     | @reflectionFlag ?F =>
       match goal with
       | R : @reflectionFlag F |- _ => specialize (H R)
       end
     | @binaryProdTypeFlag ?F =>
       match goal with
       | R : @binaryProdTypeFlag F |- _ => specialize (H R)
       end
     | @prodetaFlag ?F =>
       match goal with
       | R : @prodetaFlag F |- _ => specialize (H R)
       end
     | @universesFlag ?F =>
       match goal with
       | R : @universesFlag F |- _ => specialize (H R)
       end
     | @withpropFlag ?F =>
       match goal with
       | R : @withpropFlag F |- _ => specialize (H R)
       end
     | @withjFlag ?F =>
       match goal with
       | R : @withjFlag F |- _ => specialize (H R)
       end
     | @withemptyFlag ?F =>
       match goal with
       | R : @withemptyFlag F |- _ => specialize (H R)
       end
     | @withunitFlag ?F =>
       match goal with
       | R : @withunitFlag F |- _ => specialize (H R)
       end
     | @withboolFlag ?F =>
       match goal with
       | R : @withboolFlag F |- _ => specialize (H R)
       end
     | @prodTypeFlag ?F =>
       match goal with
       | R : @prodTypeFlag F |- _ => specialize (H R)
       end
     | @identitytypesFlag ?F =>
       match goal with
       | R : @identitytypesFlag F |- _ => specialize (H R)
       end
     end
   | H : ?P |- _ =>
     match (eval cbn in P) with
     | No => destruct H
     end
   | _ => idtac
  end).

(* Perform a tactic and deal with a configuration. *)
Tactic Notation (at level 0) "config" tactic(t) := doConfig ; t ; doConfig.

Tactic Notation (at level 5) "capply" uconstr(H) := doConfig ; apply H ; doConfig.

Tactic Notation (at level 5) "ceapply" uconstr(H) := doConfig ; eapply H ; doConfig.

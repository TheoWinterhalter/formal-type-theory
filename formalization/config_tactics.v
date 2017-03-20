Require Import config.

(* Deal with configuration. *)
Ltac doConfig :=
  (* configure the goal *)
  match goal with
  | |- ?P -> ?Q =>
    match (eval cbv in P) with
    | Yes => intros _
    | No => let H := fresh "H" in (intros H ; now elim H)
    | precondFlag =>
      let H := fresh "precondFlag" in intros H
    | reflectionFlag =>
      let H := fresh "reflectionFlag" in intros H
    | simpleproductsFlag =>
      let H := fresh "simpleproductsFlag" in intros H
    | prodetaFlag =>
      let H := fresh "prodetaFlag" in intros H
    | _ => idtac
    end
  | |- ?P =>
    match (eval cbv in P) with
    | Yes => exact yes
    end
  | H : precondFlag |- precondFlag => exact H
  | H : reflectionFlag |- reflectionFlag => exact H
  | H : simpleproductsFlag |- simpleproductsFlag => exact H
  | H : prodetaFlag |- prodetaFlag => exact H
  | _ => idtac
  end ;
  (* Configure the hypotheses *)
  repeat
  (match goal with
   | H : ?P -> ?Q |- _ =>
     match (eval cbv in P) with
     | Yes => specialize (H yes)
     | No => clear H
     | @precondFlag ?F =>
       match goal with
       | R : @precondFlag F |- _ => specialize (H R)
       end
     | @reflectionFlag ?F =>
       match goal with
       | R : @reflectionFlag F |- _ => specialize (H R)
       end
     | @simpleproductsFlag ?F =>
       match goal with
       | R : @simpleproductsFlag F |- _ => specialize (H R)
       end
     | @prodetaFlag ?F =>
       match goal with
       | R : @prodetaFlag F |- _ => specialize (H R)
       end
     end
   | H : ?P |- _ =>
     match (eval cbv in P) with
     | No => destruct H
     end
   | _ => idtac
  end).

(* Perform a tactic and deal with a configuration. *)
Tactic Notation (at level 0) "config" tactic(t) := doConfig ; t ; doConfig.

Tactic Notation (at level 5) "capply" uconstr(H) := doConfig ; apply H ; doConfig.

Tactic Notation (at level 5) "ceapply" uconstr(H) := doConfig ; eapply H ; doConfig.

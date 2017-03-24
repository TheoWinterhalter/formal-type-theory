(* Inversion theorems for ptt. *)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.

Section PttInversion.

Local Instance hasPrecond : config.Precond := {| config.precondFlag := config.Yes |}.
Context `{ConfigReflection : config.Reflection}.

Local Open Scope type_scope.

Definition CtxEqInversion G1 G2 :
  eqctx G1 G2 ->
  ((G1 = ctxempty) * (G2 = ctxempty)) +
  { D1 : context &
  { A1 : type &
  { D2 : context &
  { A2 : type &
    (G1 = ctxextend D1 A1) * (G2 = ctxextend D2 A2)
  }}}}.
Proof.
  intro eq.
  induction eq.

  - { destruct G.
      + now left.
      + rename t into A ; right.
        exists G, A, G, A ; auto.
    }

  - { destruct IHeq as [[Gempty Dempty] | H].

     - now left.
     - destruct H as (D1 & A1 & D2 & A2 & eq1 & eq2).
       right.
       now exists D2, A2, D1, A1.
    }

  - { destruct IHeq1 as [[Gempty Dempty] | [D1 [A1 [D2 [A2 [eq3 eq4]]]]]] ;
      destruct IHeq2 as [[? ?] | [D3 [A3 [D4 [A4 [eq5 eq6]]]]]].

      - now left.
      - rewrite Dempty in eq5. discriminate eq5.
      - rewrite e in eq4. discriminate eq4.
      - right.
        now exists D1, A1, D4, A4.
    }

  - now left.

  - right.
    now exists G, A, D, B.

Defined.


Definition CtxExtendInversion G A (H : isctx (ctxextend G A)) :
  isctx G * istype G A.
Proof.
  config inversion_clear H. easy.
Defined.

Fixpoint TyIdInversion G A u v (H : istype G (Id A u v)) {struct H} :
  isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  inversion H ; doConfig.

  - { split ; [(split ; [split | idtac]) | idtac].

      - assumption.
      - apply (@TyCtxConv _ _ G0 G) ; auto.
        now apply TyIdInversion with (u := u) (v := v).
      - apply (@TermCtxConv _ _ G0 G) ; auto.
        + now apply TyIdInversion with (u := u) (v:= v).
        + now config apply TyIdInversion with (u := u) (v:= v).
      - apply (@TermCtxConv _ _ G0 G) ; auto.
        + now apply TyIdInversion with (u := u) (v:= v).
        + now config apply TyIdInversion with (u := u) (v:= v).
    }

  - { split ; [(split ; [split | idtac]) | idtac].
      - assumption.
      - assumption.
      - assumption.
      - assumption.
    }

Defined.

Fixpoint TyProdInversion G A B (H : istype G (Prod A B)) {struct H} :
  isctx G * istype G A * istype (ctxextend G A) B.
Proof.
  inversion H ; doConfig.

  - { split ; [ split | idtac ].
      - assumption.
      - apply (@TyCtxConv _ _ G0 G) ; auto.
        now apply (TyProdInversion G0 A B).
      - apply (@TyCtxConv _ _ (ctxextend G0 A) (ctxextend G A)).
        + now apply (TyProdInversion G0 A B).
        + apply EqCtxExtend ; auto.
          * now capply (TyProdInversion G0 A B).
          * now capply (TyProdInversion G0 A B).
          * capply EqTyRefl ; auto.
            now apply (TyProdInversion G0 A B).
        + capply CtxExtend ; auto.
          now apply (TyProdInversion G0 A B).
        + capply CtxExtend.
          * assumption.
          * apply (@TyCtxConv _ _ G0 G) ; auto.
            now apply (TyProdInversion G0 A B).
    }

  - { split ; [ split | idtac ].
      - assumption.
      - assumption.
      - assumption.
    }
Defined.

End PttInversion.

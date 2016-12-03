(* Uniqueness of typing. *)

Require Import ett.
Require Import sanity.

Lemma eqctx_sym {G D} : eqctx G D -> eqctx D G.
Proof.
  intros [|? ? ? ?].  
  - apply EqCtxEmpty.
  - now apply EqCtxExtend, EqTySym.
Defined.

Lemma eqctx_refl G : isctx G -> eqctx G G.
Proof.
  intros [|? ? ? ?].
  - apply EqCtxEmpty.
  - now apply EqCtxExtend, EqTyRefl.
Defined.

Lemma eqctx_trans G D E :
  eqctx G D -> eqctx D E -> eqctx G E.
Proof.
  intros [|? ? ? ?].
  - intro H ; exact H.
  - intro H.
    inversion H.
    apply EqCtxExtend.
    eapply EqTyTrans.
    + eassumption.
    + assumption.
Defined.

Lemma eqctx_ctxextend G A G' A' :
  eqctx (ctxextend G A) (ctxextend G' A') ->
  ((G = G') * eqtype G A A')%type.
Proof.
  intro E.
  inversion E.
  split.
  - exact eq_refl.
  - assumption.
Defined.


(* We need something like this. *)
Hypothesis substCtxConv :
  forall G G' D sbs (E : eqctx G' G),
    issubst sbs G D -> issubst sbs G' D.

(* Hypothesis eqctx_ctx : *)
(*   forall { G D A }, *)
(*     eqctx G D -> *)
(*     eqctx (ctxextend G A) (ctxextend D A). *)

Hypothesis eqTyCongWeak :
  forall { G A A' B B' },
  eqtype G A A' ->
  eqtype G B B' ->
  eqtype (ctxextend G A) (Subst B (sbweak G A)) (Subst B' (sbweak G A')).

Hypothesis temporary :
  forall {G A B}, eqtype G A B.
  
Hypothesis temporary2 :
  forall {G D}, eqctx G D.

Ltac doTyConv unique_term' :=
  eapply EqTyTrans ;
  [ eapply unique_term' ;
    [ eassumption
    | assumption ]
  | eapply EqTyCtxConv ;
    [ eassumption
    | assumption ] ].

Ltac doCtxConv D' unique_term' :=
  eapply unique_term' ;
  [ eassumption
  | now apply (eqctx_trans _ D') ].

Fixpoint unique_term G u A (H1 : isterm G u A) {struct H1}:
  forall B D,
    isterm D u B ->
    eqctx D G ->
    eqtype G A B

with unique_subst G D1 sbs (H1 : issubst sbs G D1) {struct H1}:
  forall D2 (H2 : issubst sbs G D2),
    eqctx D1 D2.

Proof.
  (* unique_term *)
  { destruct H1 ;
    simple refine (fix unique_term' B' D' H2' H3' {struct H2'}:= _).

    (* H1: TermTyConv *)    
    - { 
        apply (@EqTyTrans G _ A B').
        + now apply EqTySym.
        + eapply (unique_term G u A) ; eassumption.
      }

    (* TermCtxConv *)
    - { 
        eapply EqTyCtxConv.
        - eapply unique_term.
          + eassumption.
          + eassumption.
          + apply (eqctx_trans _ D).
            * assumption.
            * now apply eqctx_sym.
        - assumption.
      }

    (* TermSubst *)
    - { inversion_clear H2'.
        - doTyConv unique_term'.
        - doCtxConv D' unique_term'.

        - eapply CongTySubst.
          + eassumption.
          + eapply (unique_term _ u).
            * exact H1.
            * eassumption.
            * { apply eqctx_sym.
                apply (unique_subst G _ sbs).
                - assumption.
                - eapply substCtxConv.                  
                  + eapply eqctx_sym.
                    eassumption.
                  + assumption. }
      }

    (* TermVarZero *)
    - { inversion H2'.
        - doTyConv unique_term'.
        - doCtxConv D' unique_term'.

        - { assert (L : eqctx (ctxextend G0 A0) (ctxextend G A)).
            - now rewrite H0.
            - destruct (eqctx_ctxextend _ _ _ _  L) as [E M].
              rewrite E in * |- *.
              apply eqTyCongWeak.
              + now apply EqTySym.
              + now apply EqTySym.
          }
      }


    (* TermVarSucc *)
      - { inversion H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { assert (L : eqctx (ctxextend G0 B0) (ctxextend G B)).
              - now rewrite H2.
              - destruct (eqctx_ctxextend _ _ _ _  L) as [E M].
                rewrite E in * |- *.
                apply eqTyCongWeak.
                + now apply EqTySym.
                + eapply (unique_term _ (var k)).
                  * assumption.
                  * eassumption.
                  * apply eqctx_refl.
                    now apply (@sane_isterm G A (var k)).
            }
        }

      (* TermAbs *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply temporary.

        }

      (* TermApp *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply temporary.

        }

      (* TermRefl *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply temporary.

        }

      (* TermJ *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply temporary.

        }

      (* TermExfalso *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply temporary.

        }

      (* TermUnit *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply temporary.

        }

      (* TermTrue *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply temporary.

        }

      (* TermFalse *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply temporary.

        }

      (* TermCond *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply temporary.

        }
  }

 (* unique_subst *)
 { intros;
   apply temporary2.
 }

Defined.

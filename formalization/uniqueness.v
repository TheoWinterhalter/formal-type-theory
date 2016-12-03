(* Uniqueness of typing. *)

Require Import ett.
Require Import sanity.

(* Auxiliary admissibility lemmas. *)

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

(* Auxiliary inversion lemmas. *)

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


(* It looks like we need to strengthen some inference
   rules, as follows: *)

(* Is this one admissible? *)
Hypothesis substCtxConv' :
  forall G G' D sbs (E : eqctx G' G),
    issubst sbs G D -> issubst sbs G' D.

Hypothesis eqCtxExtend' :
  forall {G D A B},
    eqctx G D ->
    eqtype G A B ->
    eqctx (ctxextend G A) (ctxextend D B).

Hypothesis eqTyCongWeak' :
  forall { G A A' B B' },
  eqtype G A A' ->
  eqtype G B B' ->
  eqtype (ctxextend G A) (Subst B (sbweak G A)) (Subst B' (sbweak G A')).

Hypothesis eqTyCongZero' :
  forall {G1 G2 A1 A2 B1 B2 u1 u2},
    eqctx G1 G2 ->
    eqtype G1 A1 B1 ->
    eqterm G1 u1 u2 A1 ->
    eqtype (ctxextend G1 A1) A2 B2 ->
    eqtype G1
           (Subst A2 (sbzero G1 A1 u1))
           (Subst B2 (sbzero G2 B1 u2)).

(* A hack to be able to admit cases and still have Coq verify
   that the fixpoints are well-defined. *)
Hypothesis temporary :
  forall {G A B}, eqtype G A B.

(* Tactics for dealing with the conversion cases. *)

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

(* The version of the theorem that allows variation of the context. *)

Fixpoint unique_term_ctx G u A (H1 : isterm G u A) {struct H1}:
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
        + eapply (unique_term_ctx G u A) ; eassumption.
      }

    (* TermCtxConv *)
    - { 
        eapply EqTyCtxConv.
        - eapply unique_term_ctx.
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
          + eapply (unique_term_ctx _ u).
            * exact H1.
            * eassumption.
            * { apply eqctx_sym.
                apply (unique_subst G _ sbs).
                - assumption.
                - eapply substCtxConv'.
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
              apply eqTyCongWeak'.
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
                apply eqTyCongWeak'.
                + now apply EqTySym.
                + eapply (unique_term_ctx _ (var k)).
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

          - apply EqTyRefl.
            + apply TyProd.
              * assumption.
              * now apply (@sane_isterm (ctxextend G A) B u).
        }

      (* TermApp *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { apply eqTyCongZero'.
              - now apply eqctx_sym.
              - now apply EqTyRefl, (@sane_isterm G A v).
              - now apply EqRefl.
              - now apply EqTyRefl.
            }
        }

      (* TermRefl *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - apply EqTyRefl, TyId.
            + now apply (@sane_isterm G A u).
            + assumption.
            + assumption.
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

          - { apply EqTyRefl.
              eapply TyCtxConv.
              + eassumption.
              + assumption. }
        }

      (* TermUnit *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply EqTyRefl, TyUnit.
        }

      (* TermTrue *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply EqTyRefl, TyBool.
        }

      (* TermFalse *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - now apply EqTyRefl, TyBool.
        }

      (* TermCond *)
      - { inversion_clear H2'.
          - doTyConv unique_term'.
          - doCtxConv D' unique_term'.

          - { apply eqTyCongZero'.
              + now apply eqctx_sym.
              + now apply EqTyRefl, TyBool, (@sane_isterm G Bool u).
              + now apply EqRefl.
              + now apply EqTyRefl.
            }
        }
  }

 (* unique_subst *)
 { intros D2 H2.
   destruct H1.

   (* H1: SubstZero *)
   - { inversion_clear H2.
       apply eqctx_refl, CtxExtend; now apply (@sane_isterm G A u).
     }

   (* H1: SubstWeak *)
   - { inversion_clear H2.
       now apply eqctx_refl, (@sane_istype D2 A).
     }

   (* H2: SubstShift *)
   - { inversion_clear H2.
       apply eqCtxExtend'.
       apply (unique_subst G _ sbs).
       + assumption.
       + assumption.
       + now apply EqTyRefl.
     }       
 }

Defined.

(* The main theorem as it will probably be used. *)
Corollary unique_term {G A B u} :
  isterm G u A ->
  isterm G u B ->
  eqtype G A B.

Proof.
  intros H1 H2.
  eapply unique_term_ctx.
  - eassumption.
  - eassumption.
  - now apply eqctx_refl, (@sane_isterm G A u).
Defined.

Require syntax. (* The syntax of ett/ptt. *)
Require ptt.
Require ctt.
Require Import eval.

Module S := syntax.
Module P := ptt.
Module C := ctt.

(* For a term in CTT to be well-typed we need to evaluate it to ITT and
   check there. *)
Definition Cisctx G := I.isctx (eval_ctx G).
Definition Cissubst sbs G D :=
  I.issubst (eval_substitution sbs) (eval_ctx G) (eval_ctx D).
Definition Cistype G A :=
  I.istype (eval_ctx G) (eval_type A).
Definition Cisterm G u A :=
  I.isterm (eval_ctx G) (eval_term u) (eval_type A).

(* We do something similar for coercions. *)
Definition CisContextCoercion c G D :=
  C.isContextCoercion c (eval_ctx G) (eval_ctx D).

(* This lemma might need to be relocated in itt or so. *)
Lemma inversion_sbcomp :
  forall {sbs sbt G D},
    I.issubst (I.sbcomp sbs sbt) G D ->
    { E : I.context &
      I.issubst sbs E D *
      I.issubst sbt G E
    }%type.
Proof.
  intros sbs sbt G D h.
  assert (
      forall sbr,
        sbr = I.sbcomp sbs sbt -> I.issubst sbr G D ->
        { E : I.context &
          I.issubst sbs E D *
          I.issubst sbt G E
        }%type
  ).
  { intros sbr eq. induction 1 ; try discriminate.
    - inversion eq. subst.
      exists D. split ; assumption.
    - subst. destruct (IHissubst H eq_refl) as [E [h1 h2]].
      exists E. split.
      + eapply I.SubstCtxConv.
        * exact h1.
        * apply I.CtxRefl.
          (* We need sanity to conclude. *)
          admit.
        * assumption.
      + eapply I.SubstCtxConv.
        * exact h2.
        * assumption.
        * apply I.CtxRefl.
          (* We need sanity to conclude. *)
          admit.
  }
  apply (H (I.sbcomp sbs sbt) eq_refl h).
Admitted.

Lemma inversion_substitution :
  forall {c1' c2' sbs' G D},
    Cissubst (C.sbcoerce (c1', c2') sbs') G D ->
    { Gi : I.context &
      { Di : I.context &
        I.issubst (C.ctxco_inv c1') (eval_ctx G) Gi *
        I.issubst (eval_substitution' sbs') Gi Di   *
        I.issubst (C.ctxco_map c2') Di (eval_ctx D)
      }
    }%type.
Proof.
  intros c1' c2' sbs' G D h.
  unfold Cissubst in h. simpl in h.
  destruct (inversion_sbcomp h) as [E1 [h1 h2]].
  destruct (inversion_sbcomp h2) as [E2 [h3 h4]].
  exists E2, E1. repeat split ; assumption.
Defined.

(* Some lemma to apply a coercion to a substitution rather than on a
   substitution' *)
Definition coerce_substitution (sbs : C.substitution) (sc : C.substCoerce)
  : C.substitution
  := match sbs,sc with
    | C.sbcoerce (c1',c2') sbs', (c1,c2) =>
      C.sbcoerce (C.contextComp c1 c1', C.contextComp c2 c2') sbs'
    end.

Lemma coerce_substitution_typing
  { sbs c1 c2 G D G' D' }
  (hsbs : Cissubst sbs G D)
  (hc1 : CisContextCoercion c1 G G') (hc2 : CisContextCoercion c2 D D')
  : Cissubst (coerce_substitution sbs (c1,c2)) G' D'.
Proof.
  unfold coerce_substitution. destruct sbs as [[c1' c2'] sbs'].
  unfold Cissubst. simpl.
  destruct (inversion_substitution hsbs) as (Gi & Di & [[h1 h2] h3]).
  eapply I.SubstComp.
  - eapply I.SubstComp.
    + eapply I.SubstComp.
      * destruct hc1 as [[_ h] _]. exact h.
      * eassumption.
    + eassumption.
  - eapply I.SubstComp.
    + eassumption.
    + destruct hc2 as [[h _] _]. exact h.
Defined.

(* Same thing but on a type. *)
Lemma inversion_Subst :
  forall { G A sbs },
    I.istype G (I.Subst A sbs) ->
    { D : I.context &
      I.issubst sbs G D *
      I.istype D A
    }%type.
Proof.
  intros G A sbs h.
  assert (
    forall B,
      B = I.Subst A sbs ->
      I.istype G B ->
      { D : I.context &
        I.issubst sbs G D *
        I.istype D A
      }%type
  ).
  { intros B eq. induction 1 ; try discriminate.
    - subst. destruct (IHistype H eq_refl) as [E [h1 h2]].
      exists E. split.
      + eapply I.SubstCtxConv.
        * eassumption.
        * assumption.
        * (* Once again we need sanity for ITT *)
          apply I.CtxRefl.
          admit.
      + assumption.
    - inversion eq. subst.
      exists D. split ; assumption.
  }
  apply (H (I.Subst A sbs) eq_refl h).
Admitted.

Lemma inversion_type :
  forall {G c' A'},
    Cistype G (C.Coerce c' A') ->
    { D : I.context &
      I.issubst (C.ctxco_inv c') (eval_ctx G) D *
      I.istype D (eval_type' A')
    }%type.
Proof.
  intros G c' A' h.
  unfold Cistype in h. simpl in h.
  destruct (inversion_Subst h) as [E [h1 h2]].
  exists E. split ; assumption.
Defined.

Definition coerce_type (A : C.type) (tc : C.typeCoerce) : C.type :=
  match A with
  | C.Coerce c A' =>
    C.Coerce (C.contextComp tc c) A'
  end.

Lemma coerce_type_typing
  { G D A c }
  (hA : Cistype G A)
  (hc : CisContextCoercion c G D)
  : Cistype D (coerce_type A c).
Proof.
  unfold coerce_type. destruct A as [c' A'].
  unfold Cistype. simpl.
  destruct (inversion_type hA) as [E [h1 h2]].
  eapply I.TySubst.
  - eapply I.SubstComp.
    + destruct hc as [[_ h] _]. exact h.
    + eassumption.
  - assumption.
Defined.


(* "hml" stands for "homologous" which is too long to type. *)

Inductive hml_context :
  S.context -> C.context -> Type :=

  | hml_ctxempty :
      hml_context S.ctxempty C.ctxempty

  | hml_ctxextend :
      forall {G G' A A'},
        hml_context G G' ->
        hml_type A A' ->
        hml_context (S.ctxextend G A) (C.ctxextend G' A')

with hml_substitution :
  S.substitution -> C.substitution -> Type :=

  | hml_sbzero :
      forall {G G' A A' u u' c},
        hml_context G G' ->
        hml_type A A' ->
        hml_term u u' ->
        hml_substitution (S.sbzero G A u) (C.sbcoerce c (C.sbzero G' A' u'))

  | hml_sbweak :
      forall {G G' A A' c},
        hml_context G G' ->
        hml_type A A' ->
        hml_substitution (S.sbweak G A) (C.sbcoerce c (C.sbweak G' A'))

  | hml_sbshift :
      forall {G G' A A' sbs sbs' c},
        hml_context G G' ->
        hml_type A A' ->
        hml_substitution sbs sbs' ->
        hml_substitution (S.sbshift G A sbs)
                         (C.sbcoerce c (C.sbshift G' A' sbs'))

  | hml_sbid :
      forall {G G' c},
        hml_context G G' ->
        hml_substitution (S.sbid G) (C.sbcoerce c (C.sbid G'))

  | hml_sbcomp :
      forall {sbs sbs' sbt sbt' c},
        hml_substitution sbs sbs' ->
        hml_substitution sbt sbt' ->
        hml_substitution (S.sbcomp sbs sbt)
                         (C.sbcoerce c (C.sbcomp sbs' sbt'))

with hml_type :
  S.type -> C.type -> Type :=

  | hml_Prod :
      forall {A A' B B' c},
        hml_type A A' ->
        hml_type B B' ->
        hml_type (S.Prod A B) (C.Coerce c (C.Prod A' B'))

  | hml_Id :
      forall {A A' u u' v v' c},
        hml_type A A' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_type (S.Id A u v) (C.Coerce c (C.Id A' u' v'))

  | hml_Subst :
      forall {A A' sbs sbs' c},
        hml_type A A' ->
        hml_substitution sbs sbs' ->
        hml_type (S.Subst A sbs) (C.Coerce c (C.Subst A' sbs'))

  | hml_Empty :
      forall {c},
        hml_type S.Empty (C.Coerce c C.Empty)

  | hml_Unit :
      forall {c},
        hml_type S.Unit (C.Coerce c C.Unit)

  | hml_Bool :
      forall {c},
        hml_type S.Bool (C.Coerce c C.Bool)

with hml_term :
  S.term -> C.term -> Type :=

  | hml_var {k c} :
      hml_term (S.var k) (C.coerce c (C.var k))

  | hml_lam :
      forall {A A' B B' u u' c},
        hml_type A A' ->
        hml_type B B' ->
        hml_term u u' ->
        hml_term (S.lam A B u) (C.coerce c (C.lam A' B' u'))

  | hml_app :
      forall {A A' B B' u u' v v' c},
        hml_type A A' ->
        hml_type B B' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_term (S.app u A B v)
                 (C.coerce c (C.app u' A' B' v'))

  | hml_refl :
      forall {A A' u u' c},
        hml_type A A' ->
        hml_term u u' ->
        hml_term (S.refl A u) (C.coerce c (C.refl A' u'))

  | hml_j :
      forall {A A' C C' u u' v v' w w' p p' c},
        hml_type A A' ->
        hml_type C C' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_term w w' ->
        hml_term p p' ->
        hml_term (S.j A u C w v p)
                 (C.coerce c (C.j A' u' C' w' v' p'))

  | hml_subst :
      forall {u u' sbs sbs' c},
        hml_term u u' ->
        hml_substitution sbs sbs' ->
        hml_term (S.subst u sbs)
                 (C.coerce c (C.subst u' sbs'))

  | hml_exfalso :
      forall {A A' u u' c},
        hml_type A A' ->
        hml_term u u' ->
        hml_term (S.exfalso A u) (C.coerce c (C.exfalso A' u'))

  | hml_unit :
      forall {c},
        hml_term S.unit (C.coerce c C.unit)

  | hml_true :
      forall {c},
        hml_term S.true (C.coerce c C.true)

  | hml_false :
      forall {c},
        hml_term S.false (C.coerce c C.false)

  | hml_cond :
      forall {C C' u u' v v' w w' c},
        hml_type C C' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_term w w' ->
        hml_term (S.cond C u v w)
                 (C.coerce c (C.cond C' u' v' w'))

.

Definition hml_substitution_change
    sc1 sc2 sbs sbs'
    (h : hml_substitution sbs (C.sbcoerce sc1 sbs'))
  : hml_substitution sbs (C.sbcoerce sc2 sbs')
  := match h with
    | hml_sbzero h1 h2 h3  => hml_sbzero h1 h2 h3
    | hml_sbweak h1 h2     => hml_sbweak h1 h2
    | hml_sbshift h1 h2 h3 => hml_sbshift h1 h2 h3
    | hml_sbid h1          => hml_sbid h1
    | hml_sbcomp h1 h2     => hml_sbcomp h1 h2
    end.

Definition hml_type_change
    c1 c2 A A'
    (h : hml_type A (C.Coerce c1 A'))
  : hml_type A (C.Coerce c2 A')
  := match h with
    | hml_Prod h1 h2  => hml_Prod h1 h2
    | hml_Id h1 h2 h3 => hml_Id h1 h2 h3
    | hml_Subst h1 h2 => hml_Subst h1 h2
    | hml_Empty       => hml_Empty
    | hml_Unit        => hml_Unit
    | hml_Bool        => hml_Bool
    end.

Definition hml_type_coerce
    c A A'
    (h : hml_type A A')
  : hml_type A (coerce_type A' c).
Proof.
  destruct A' as [A' c'].
  eapply hml_type_change.
  eassumption.
Defined.


Structure istrans_ctx (G : S.context) (G' : C.context) :=
  {
    isctx_derive : Cisctx G' ;
    isctx_hom : hml_context G G'
  }.

Structure istrans_subst
          (sbs : S.substitution)
          (G' D' : C.context) (sbs' : C.substitution)
  :=
  {
    issubst_derive : Cissubst sbs' G' D' ;
    issubst_hom : hml_substitution sbs sbs'
  }.

Structure istrans_type (A : S.type) (G' : C.context) (A' : C.type) :=
  {
    istype_derive : Cistype G' A' ;
    istype_hom : hml_type A A'
  }.

Structure istrans_term (u : S.term) (G' : C.context) (u' : C.term) (A' : C.type) :=
  {
    isterm_derive : Cisterm G' u' A' ;
    isterm_hom : hml_term u u'
  }.

(* Notion of equivalences. *)
Parameter equiv_type : C.context -> C.type -> C.type -> Type.
Parameter equiv_term : C.context -> C.term -> C.term -> C.type -> Type.
(* Should we use coercions as the corresponding definition for equiv_type? *)

(* Seems like this notation screws up the other one. *)
(* Notation "{ x : A & y : B & P }" := *)
(*   (sigT (A:=A) (fun x => sigT (A:=B) (fun y => P))) *)
(*   : type_scope. *)

Ltac todo := exact todo.

Fixpoint trans_ctx {G} (H : P.isctx G) {struct H} :
  { G' : C.context & istrans_ctx G G' }

with trans_subst_left {G G' D sbs} (H : P.issubst sbs G D)
                  (Ht : istrans_ctx G G') {struct H} :
       { D' : C.context &
         istrans_ctx D D' *
         { sbt : C.substitution & istrans_subst sbs G' D' sbt } }%type

(* this one might not be needed? *)
(* with trans_subst_right {G D D' sbs} (H : E.issubst sbs G D) *)
(*                   (Ht : istrans_ctx D D') {struct H} : *)
(*        { G' : C.context & { sbt : C.substitution & C.issubst sbt G' D' } } *)

with trans_type {G G' A} (H : P.istype G A) (Ht : istrans_ctx G G') {struct H} :
       { A' : C.type &
              istrans_type A G' A' *
              (* this component might not be needed? *)
              forall A'' (Hty : istrans_type A G' A''), equiv_type G' A' A''
       }%type

with trans_term
       {G u A G' A'}
       (H : P.isterm G u A)
       (HG : istrans_ctx G G')
       (HA : istrans_type A G' A') {struct H}
     : { u' : C.term &
         istrans_term u G' u' A' *
         (* this component might not be needed? *)
         forall u'' (Hu : istrans_term u G' u'' A'), equiv_term G' u' u'' A'
       }%type

with trans_eqctx_left
       {G G' D}
       (H : P.eqctx G D)
       (HG : istrans_ctx G G') {struct H}
     : { D' : C.context &
         istrans_ctx D D' *
         { c : C.contextCoercion &
           CisContextCoercion c G' D'
         }
       }%type

with trans_eqctx_right
       {G D D'}
       (H : P.eqctx G D)
       (HD : istrans_ctx D D') {struct H}
     : { G' : C.context &
         istrans_ctx G G' *
         { c : C.contextCoercion &
           CisContextCoercion c G' D'
         }
       }%type.

Proof.
  (****** trans_ctx ******)
  - { destruct H.

      (* CtxEmpty *)
      - exists C.ctxempty.
        split.
        + constructor.
        + constructor.

      (* CtxExtend *)
      - destruct (trans_ctx _ H) as [G' HGisG'].
        destruct (trans_type G G' A i HGisG') as (A' & HAisA' & _).
        exists (C.ctxextend G' A').
        split.
        + constructor.
          now destruct HAisA'.
        + constructor.
          * now destruct HGisG'.
          * now destruct HAisA'.
    }

  (****** trans_subst_left ******)
  - { destruct H.

      (* SubstZero *)
      - destruct (trans_type G G' A i0 Ht) as (A' & HAisA' & _).
        destruct (trans_term G u A G' A' i Ht HAisA') as (u' & Huisu' & _).
        exists (C.ctxextend G' A').
        { split.
          - constructor.
            + unfold Cisctx. simpl.
              apply I.CtxExtend.
              now inversion HAisA'.
            + constructor.
              * now inversion Ht.
              * now inversion HAisA'.
          - exists (C.sbcoerce
                 (C.idSb
                    (eval_ctx G')
                    (itt.ctxextend (eval_ctx G') (eval_type A')))
                 (C.sbzero G' A' u')).
            split.
            + unfold Cissubst. simpl.
              { eapply I.SubstComp.
                - eapply I.SubstComp.
                  + eapply I.SubstId. now inversion Ht.
                  + eapply I.SubstZero. now inversion Huisu'.
                - apply I.SubstId. eapply I.CtxExtend.
                  now inversion HAisA'.
              }
            + constructor.
              * now destruct Ht.
              * now destruct HAisA'.
              * now destruct Huisu'.
        }

      (* SubstWeak *)
      - destruct Ht as [HG' hom].
        inversion hom. subst.
        exists G'0.
        { split.
          - constructor.
            + todo. (* We need sanity *)
            + assumption.
          - exists (C.sbcoerce
                 (C.idSb
                    (itt.ctxextend (eval_ctx G'0) (eval_type A'))
                    (eval_ctx G'0))
                 (C.sbweak G'0 A')).
            split.
            + (* To type it we need to recover that A' is a type. *)
              inversion HG'. subst.
              (* We need to now how to evaluate coercions. *)
              unfold Cissubst. simpl.
              { eapply I.SubstComp.
                - eapply I.SubstComp.
                  + eapply I.SubstId. assumption.
                  + eapply I.SubstWeak. assumption.
                - eapply I.SubstId. todo. (* We need sanity *)
              }
            + constructor ; assumption.
        }

      (* SubstShift *)
      - destruct Ht as [HG' hom].
        inversion hom. subst.
        rename G'0 into G'. rename X into homG. rename X0 into homAs.
        inversion homAs. subst.
        rename A'0 into A'. rename X into homA. rename X0 into homs.
        (* What we probably want is something similar to the other
           translation functions where we can take in some homologous
           object to build a path between them? *)

        (* We probably want to use sbs' that we already have. *)
        (* assert (HtG : istrans_ctx G G'0). *)
        (* { split. *)
        (*   - now inversion HG'. *)
        (*   - assumption. *)
        (* } *)
        (* destruct (trans_subst_left G G'0 D sbs H HtG) as [D' [sbt h]]. *)
        (* exists (C.ctxextend D' A'0). exists () *)
        inversion HG'. subst.
        (* Now that's great, but the inversion doesn't give us that A'σ' is well
           typed and thus that σ' is as well, yielding a Δ' for us to play with.
         *)
        todo.

      (* SubstId *)
      - exists G'.
        split ; try assumption.
        exists (C.sbcoerce (C.idSb (eval_ctx G') (eval_ctx G')) (C.sbid G')).
        split.
        + unfold Cissubst. simpl.
          { eapply I.SubstComp.
            - eapply I.SubstComp.
              + eapply I.SubstId. now inversion Ht.
              + eapply I.SubstId. now inversion Ht.
            - eapply I.SubstId. now inversion Ht.
          }
        + constructor. now destruct Ht.

      (* SubstComp *)
      - destruct (trans_subst_left G G' D sbs H Ht) as (D' & HD' & sbs' & Hsbs).
        destruct (trans_subst_left D D' E sbt H0 HD') as (E' & HE' & sbt' & ?).
        exists E'.
        split.
        + assumption.
        + exists (C.sbcoerce
               (C.idSb (eval_ctx G') (eval_ctx E'))
               (C.sbcomp sbt' sbs')).
          { split.
            - unfold Cissubst. simpl.
              eapply I.SubstComp.
              + { eapply I.SubstComp.
                  - eapply I.SubstId. now inversion Ht.
                  - eapply I.SubstComp.
                    + inversion Hsbs. eassumption.
                    + inversion i2. eassumption.
                }
              + eapply I.SubstId. now inversion HE'.
            - constructor.
              + now inversion i2.
              + now inversion Hsbs.
          }

      (* SubstCtxConv *)
      - rename G' into G2'.
        destruct (trans_eqctx_right G1 G2 G2' e Ht) as (G1' & HG1 & c1 & Hc1).
        destruct (trans_subst_left G1 G1' D1 sbs H HG1)
          as (D1' & HD1 & sbs' & Hsbs).
        destruct (trans_eqctx_left D1 D1' D2 e0 HD1) as (D2' & HD2 & c2 & Hc2).
        exists D2'.
        split.
        + assumption.
        + exists (coerce_substitution sbs' (c1,c2)).
          split.
          * { eapply coerce_substitution_typing.
              - destruct Hsbs. eassumption.
              - eassumption.
              - eassumption.
            }
          * destruct Hsbs as [_ hml].
            unfold coerce_substitution. destruct sbs'. destruct s.
            eapply hml_substitution_change. eassumption.
    }

  (****** trans_subst_right ******)
  (* - { destruct H. *)

  (*     (* SubstZero *) *)
  (*     - admit. *)

  (*     (* SubstWeak *) *)
  (*     - admit. *)

  (*     (* SubstShift *) *)
  (*     - admit. *)

  (*     (* SubstId *) *)
  (*     - admit. *)

  (*     (* SubstComp *) *)
  (*     - admit. *)

  (*     (* SubstCtxConv *) *)
  (*     - admit. *)
  (*   } *)

  (****** trans_type ******)
  - { destruct H.

      (* TyCtxConv *)
      - rename G' into D'.
        destruct (trans_eqctx_right G D D' e Ht) as (G' & HGisG' & c & Hc).
        destruct (trans_type G G' A H HGisG') as [A' [HA fA]].
        exists (coerce_type A' c). split.
        + { split.
            - eapply coerce_type_typing.
              + destruct HA. eassumption.
              + assumption.
            - destruct HA.
              unfold coerce_type. destruct A'.
              eapply hml_type_change. eassumption.
          }
        + todo. (* Same as always, we need to be sure what an equivalence is. *)

      (* TySubst *)
      - destruct (trans_subst_left G G' D sbs i Ht) as [D' [HD [sbt Hsbt]]].
        destruct (trans_type D D' A H HD) as [A' [HAisA' fA]].
        exists (C.Coerce (C.idTy (eval_ctx G')) (C.Subst A' sbt)).
        split.
        + split.
          * { unfold Cistype. simpl.
              eapply I.TySubst.
              - eapply I.SubstId. now destruct Ht.
              - eapply I.TySubst.
                + destruct Hsbt. eassumption.
                + destruct HAisA'. assumption.
            }
          * { apply hml_Subst.
              - now destruct HAisA'.
              - now destruct Hsbt.
            }
        + todo. (* Same again. *)

      (* TyProd *)
      - destruct (trans_type G G' A H0 Ht) as [A' [HAisA' fA]].
        pose (Gx := syntax.ctxextend G A).
        pose (Gx' := C.ctxextend G' A').
        assert (Hex : istrans_ctx Gx Gx').
        { split.
          - unfold Cisctx. simpl.
            apply I.CtxExtend.
            destruct HAisA'. assumption.
          - apply hml_ctxextend.
            + destruct Ht. assumption.
            + destruct HAisA'. assumption.
        }
        destruct (trans_type Gx Gx' B H Hex) as [B' [HBisB' fB]].
        exists (C.Coerce (C.idTy (eval_ctx G')) (C.Prod A' B')).
        split.
        + { split.
            - unfold Cistype. simpl.
              eapply I.TySubst.
              + eapply I.SubstId. now destruct Ht.
              + eapply I.TyProd.
                now destruct HBisB'.
            - apply hml_Prod.
              + now destruct HAisA'.
              + now destruct HBisB'.
          }
        + todo. (* Same here. *)

      (* TyId *)
      - destruct (trans_type G G' A H Ht) as [A' [HA fA]].
        destruct (trans_term G u A G' A' i0 Ht HA) as [u' [Hu fu]].
        destruct (trans_term G v A G' A' i1 Ht HA) as [v' [Hv fv]].
        exists (C.Coerce (C.idTy (eval_ctx G')) (C.Id A' u' v')).
        split.
        + split.
          * { unfold Cistype. simpl.
              eapply I.TySubst.
              - eapply I.SubstId. now destruct Ht.
              - eapply I.TyId.
                + now destruct Hu.
                + now destruct Hv.
            }
          * destruct HA ; destruct Hu ; destruct Hv ; now constructor.
        + intros A'' HA''.
          (* Without a notion of equivalence, no hope to complete this goal. *)
          todo.

      (* TyEmpty *)
      - exists (C.Coerce (C.idTy (eval_ctx G')) C.Empty). split.
        + split.
          * { unfold Cistype. simpl.
              eapply I.TySubst.
              - eapply I.SubstId. now destruct Ht.
              - eapply I.TyEmpty. now destruct Ht.
            }
          * constructor.
        + intros A'' HA''. (* destruct HA'' as [H hom]. *)
          (* inversion hom. subst. *)
          todo.

      (* TyUnit *)
      - exists (C.Coerce (C.idTy (eval_ctx G')) C.Unit). split.
        + split.
          * { unfold Cistype. simpl.
              eapply I.TySubst.
              - eapply I.SubstId. now destruct Ht.
              - eapply I.TyUnit. now destruct Ht.
            }
          * constructor.
        + todo.

      (* TyBool *)
      - exists (C.Coerce (C.idTy (eval_ctx G')) C.Bool). split.
        + split.
          * { unfold Cistype. simpl.
              eapply I.TySubst.
              - eapply I.SubstId. now destruct Ht.
              - eapply I.TyBool. now destruct Ht.
            }
          * constructor.
        + todo.

    }

  (****** trans_term ******)
  - { destruct H.

      (* TermTyConv *)
      - { rename A' into B'.
          (* We need to be able to translate type equalities. *)
          (* destruct (trans_term _ _ _ _ _ H HG) *)
          todo.
        }

      (* TermCtxConv *)
      - { rename G' into D'. rename HG into HD.
          destruct (trans_eqctx_right _ _ _ e HD) as [G' [HG [c Hc]]].
          assert (HA' : istrans_type A G' (coerce_type A' (C.contextInv c))).
          { destruct HA as [HtA HhA].
            split.
            - eapply coerce_type_typing.
              + eassumption.
              + eapply C.isCoercionContextInv. assumption.
            - apply hml_type_coerce. assumption.
          }
          destruct (trans_term _ _ _ _ _ H HG HA') as [u' [Hu fu]].
          (* We need to coerce the term as well *)
          todo.
        }

      (* TermSubst *)
      - { rename A' into As'.
          destruct HA as [HtAs HhAs].
          inversion HhAs. subst.
          (* We need to know sbs' is a translation of sbs and get the
             corresponding D' as well. *)
          (* exists (C.coerce (C.idTm (eval_ctx G') (eval_type A')) (C.subst u' sbs')). *)
          todo.
        }

      (* TermVarZero *)
      - { rename G' into GA'. rename A' into Aw'.
          exists (C.coerce (C.idTm (eval_ctx GA') (eval_type Aw')) (C.var 0)).
          split.
          - split.
            + unfold Cisterm. simpl.
              eapply I.TermTyConv.
              * eapply I.TermApp.
                -- todo.
                -- todo.
              * todo.
            + constructor.
          - todo.
        }

      (* TermVarSucc *)
      - todo.

      (* TermAbs *)
      - todo.

      (* TermApp *)
      - todo.

      (* TermRefl *)
      - todo.

      (* TermJ *)
      - todo.

      (* TermExfalso *)
      - todo.

      (* TermUnit *)
      - todo.

      (* TermTrue *)
      - todo.

      (* TermFalse *)
      - todo.

      (* TermCond *)
      - todo.
    }

  (****** trans_eqctx_left ******)
  - { destruct H.

      (* CtxRefl *)
      - exists G'. split.
        + assumption.
        + exists (C.contextId (eval_ctx G')).
          unfold CisContextCoercion. apply C.isCoercionContextId.
          now destruct HG.

      (* CtxSym *)
      - rename G' into D'. rename HG into HD.
        destruct (trans_eqctx_right G D D' H HD) as [G' [HG [c Hc]]].
        exists G'. split.
        + assumption.
        + exists (C.contextInv c).
          eapply C.isCoercionContextInv. assumption.

      (* CtxTrans *)
      - destruct (trans_eqctx_left G G' D H HG) as [D' [HD [c1 Hc1]]].
        destruct (trans_eqctx_left D D' E H0 HD) as [E' [HE [c2 Hc2]]].
        exists E'. split.
        + assumption.
        + exists (C.contextComp c2 c1).
          eapply C.isCoercionContextComp ; eassumption.

      (* EqCtxEmpty *)
      - exists G'. split.
        + assumption.
        + exists (C.contextId (eval_ctx G')).
          unfold CisContextCoercion. apply C.isCoercionContextId.
          now destruct HG.

      (* EqCtxExtend *)
      - destruct HG as [HGA Hhom]. inversion Hhom. subst.
        rename X into homG. rename X0 into homA. rename G'0 into G'.
        inversion HGA. subst.
        assert (HGisG' : istrans_ctx G G').
        { split.
          - todo. (* We need sanity *)
          - assumption.
        }
        destruct (trans_eqctx_left G G' D H HGisG') as [D' [HD [cc Hcc]]].
        (* We now need to be able to translate type equalities. *)
        todo.

    }

  (****** trans_eqctx_right ******)
  - { destruct H.

      (* CtxRefl *)
      - rename D' into G'. rename HD into HG.
        exists G'. split.
        + assumption.
        + exists (C.contextId (eval_ctx G')).
          unfold CisContextCoercion. apply C.isCoercionContextId.
          now destruct HG.

      (* CtxSym *)
      - rename D' into G'. rename HD into HG.
        destruct (trans_eqctx_left G G' D H HG) as [D' [HD [c Hc]]].
        exists D'. split.
        + assumption.
        + exists (C.contextInv c).
          eapply C.isCoercionContextInv. assumption.

      (* CtxTrans *)
      - rename HD into HE. rename D' into E'.
        destruct (trans_eqctx_right D E E' H0 HE) as [D' [HD [c2 Hc2]]].
        destruct (trans_eqctx_right G D D' H HD) as [G' [HG [c1 Hc1]]].
        exists G'. split.
        + assumption.
        + exists (C.contextComp c2 c1).
          eapply C.isCoercionContextComp ; eassumption.

      (* EqCtxEmpty *)
      - rename D' into G'. rename HD into HG.
        exists G'. split.
        + assumption.
        + exists (C.contextId (eval_ctx G')).
          unfold CisContextCoercion. apply C.isCoercionContextId.
          now destruct HG.

      (* EqCtxExtend *)
      - destruct HD as [HDB Hhom]. inversion Hhom. subst.
        rename X into homD. rename X0 into homB.
        rename G' into D'. rename A' into B'.
        inversion HDB. subst.
        assert (HDisD' : istrans_ctx D D').
        { split.
          - todo. (* Sanity *)
          - assumption.
        }
        destruct (trans_eqctx_right G D D' H HDisD') as [G' [HG [cc Hcc]]].
        (* We now need to be able to translate type equalities. *)
        todo.

    }

Defined.

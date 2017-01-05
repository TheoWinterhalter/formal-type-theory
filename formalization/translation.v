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

Parameter equiv_type : C.context -> C.type -> C.type -> Type.

Parameter equiv_term : C.context -> C.term -> C.term -> C.type -> Type.

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
              { sbt : C.substitution & istrans_subst sbs G' D' sbt } }

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
      (* this is the reason we changed CtxExtend to include "isctx G". *)
      - destruct (trans_ctx _ H) as [G' HGisG'].
        destruct (trans_type G G' A i HGisG') as (A' & HAisA' & _).
        exists (C.ctxextend G' A').
        split.
        + constructor.
          * now destruct HGisG'.
          * now destruct HAisA'.
        + constructor.
          * now destruct HGisG'.
          * now destruct HAisA'.
    }

  (****** trans_subst_left ******)
  - { destruct H.

      (* SubstZero *)
      - destruct (trans_type G G' A i0 Ht) as (A' & HAisA' & _).
        destruct (trans_term G u A G' A' i1 Ht HAisA') as (u' & Huisu' & _).
        exists (C.ctxextend G' A').
        exists (C.sbcoerce C.idSb (C.sbzero G' A' u')).
        split.
        + (* unfold Cissubst. simpl. *)
          todo. (* We need to know who is idSb. *)
        + constructor.
          * now destruct Ht.
          * now destruct HAisA'.
          * now destruct Huisu'.

      (* SubstWeak *)
      - destruct Ht as [HG' hom].
        inversion hom. subst.
        exists G'0. exists (C.sbcoerce C.idSb (C.sbweak G'0 A')).
        split.
        + (* To type it we need to recover that A' is a type. *)
          inversion HG'. subst.
          (* We need to now how to evaluate coercions. *)
          todo.
        + constructor ; assumption.

      (* SubstShift *)
      - destruct Ht as [HG' hom].
        inversion hom. subst.
        inversion X0. subst.
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
      - exists G'. exists (C.sbcoerce C.idSb (C.sbid G')).
        split.
        + todo.
        + constructor. now destruct Ht.

      (* SubstComp *)
      - todo.

      (* SubstCtxConv *)
      - todo.
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
      - todo.

      (* TySubst *)
      - todo.

      (* TyProd *)
      - todo.

      (* TyId *)
      - destruct (trans_type G G' A H Ht) as [A' [HA fA]].
        destruct (trans_term G u A G' A' i0 Ht HA) as [u' [Hu fu]].
        destruct (trans_term G v A G' A' i1 Ht HA) as [v' [Hv fv]].
        exists (C.Coerce (C.idTy (eval_ctx G')) (C.Id A' u' v')).
        split.
        + split.
          * todo.
          * destruct HA ; destruct Hu ; destruct Hv ; now constructor.
        + intros A'' HA''.
          (* Without a notion of equivalence, no hope to complete this goal. *)
          todo.

      (* TyEmpty *)
      - exists (C.Coerce (C.idTy (eval_ctx G')) C.Empty). split.
        + split.
          * todo.
          * constructor.
        + intros A'' HA''. destruct HA'' as [H hom].
          inversion hom. subst.
          todo.

      (* TyUnit *)
      - exists (C.Coerce (C.idTy (eval_ctx G')) C.Unit). split.
        + split.
          * todo.
          * constructor.
        + todo.

      (* TyBool *)
      - todo.

    }

  (****** trans_term ******)
  - todo.

Defined.

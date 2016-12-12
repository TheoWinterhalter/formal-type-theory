Require ett.
Require ctt.

Module E := ett.
Module C := ctt.

(* "hml" stands for "homologous" which is too long to type. *)

Inductive hml_context :
  E.context -> C.context -> Type :=

  | hml_ctxempty :
      hml_context E.ctxempty C.ctxempty

  | hml_ctxextend :
      forall {G G' A A'},
        hml_context G G' ->
        hml_type A A' ->
        hml_context (E.ctxextend G A) (C.ctxextend G' A')

with hml_substitution :
  E.substitution -> C.substitution -> Type :=

  | hml_sbzero :
      forall {G G' A A' u u' c},
        hml_context G G' ->
        hml_type A A' ->
        hml_term u u' ->
        hml_substitution (E.sbzero G A u) (C.sbcoerce c (C.sbzero G' A' u'))

with hml_type :
  E.type -> C.type -> Type :=

  | hml_Id :
      forall {A A' u u' v v' c},
        hml_type A A' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_type (E.Id A u v) (C.Coerce c (C.Id A' u' v'))

with hml_term :
  E.term -> C.term -> Type :=

  | hml_var {k c} :
      hml_term (E.var k) (C.coerce c (C.var k))

.

Structure istrans_ctx (G : E.context) (G' : C.context) :=
  {
    isctx_derive : C.isctx G' ;
    isctx_hom : hml_context G G'
  }.

Structure istrans_subst
          (sbs : E.substitution)
          (G' D' : C.context) (sbs' : C.substitution)
  :=
  {
    issubst_derive : C.issubst sbs' G' D' ;
    issubst_hom : hml_substitution sbs sbs'
  }.

Structure istrans_type (A : E.type) (G' : C.context) (A' : C.type) :=
  {
    istype_derive : C.istype G' A' ;
    istype_hom : hml_type A A'
  }.

Structure istrans_term (u : E.term) (G' : C.context) (u' : C.term) (A' : C.type) :=
  {
    isterm_derive : C.isterm G' u' A' ;
    isterm_hom : hml_term u u'
  }.

Parameter equiv_type : C.context -> C.type -> C.type -> Type.

Parameter equiv_term : C.context -> C.term -> C.term -> C.type -> Type.

(* Seems like this notation screws up the other one. *)
(* Notation "{ x : A & y : B & P }" := *)
(*   (sigT (A:=A) (fun x => sigT (A:=B) (fun y => P))) *)
(*   : type_scope. *)

Fixpoint trans_ctx {G} (H : E.isctx G) {struct H} :
  { G' : C.context & istrans_ctx G G' }

with trans_subst_left {G G' D sbs} (H : E.issubst sbs G D)
                  (Ht : istrans_ctx G G') {struct H} :
       { D' : C.context &
              { sbt : C.substitution & istrans_subst sbs G' D' sbt } }

(* this one might not be needed? *)
(* with trans_subst_right {G D D' sbs} (H : E.issubst sbs G D) *)
(*                   (Ht : istrans_ctx D D') {struct H} : *)
(*        { G' : C.context & { sbt : C.substitution & C.issubst sbt G' D' } } *)

with trans_type {G G' A} (H : E.istype G A) (Ht : istrans_ctx G G') {struct H} :
       { A' : C.type &
              istrans_type A G' A' *
              (* this component might not be needed? *)
              forall A'' (Hty : istrans_type A G' A''), equiv_type G' A' A''
       }%type

with trans_term
       {G u A G' A'}
       (H : E.isterm G u A)
       (HG : istrans_ctx G G')
       (HA : istrans_type A G' A') {struct H}
     : { u' : C.term &
              istrans_term u G' u' A' *
              (* this component might not be needed? *)
              forall u'' (Hu : istrans_term u G' u'' A'), equiv_term G' u' u'' A'
       }%type.

Proof.
  (****** trans_ctx ******)
  - { induction H.

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
  - { induction H.

      (* SubstZero *)
      - (* We have a problem again, how do we translate A? *)
        (* It would be nice if we didn't need trans_subst_left...
           But it is needed by TySubst for instance. *)
        admit.

      (* SubstWeak *)
      - destruct Ht as [HG' hom].
        inversion hom. subst.
        exists G'0. exists (C.sbcoerce C.idSb (C.sbweak G'0 A')).
        (* We need to know istype G'0 A', however, it is unclear how to get it
           unless by using inversion, but I assume we would like to avoid that.
         *)
        admit.

      (* SubstShift *)
      - admit.

      (* SubstId *)
      - admit.

      (* SubstComp *)
      - admit.

      (* SubstCtxConv *)
      - admit.
    }

  (****** trans_subst_right ******)
  (* - { induction H. *)

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
Abort.

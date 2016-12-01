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

Fixpoint trans_ctx {G} (H : E.isctx G) {struct H} :
  { G' : C.context & istrans_ctx G G' }

with trans_subst_left {G G' D sbs} (H : E.issubst sbs G D)
                  (Ht : istrans_ctx G G') {struct H} :
       { D' : C.context & { sbt : C.substitution & C.issubst sbt G' D' } }

(* this one might not be needed? *)
with trans_subst_right {G D D' sbs} (H : E.issubst sbs G D)
                  (Ht : istrans_ctx D D') {struct H} :
       { G' : C.context & { sbt : C.substitution & C.issubst sbt G' D' } }

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
      + admit.
      + constructor.

    (* CtxExtend *)
    (* this is the reason we changed CtxExtend to include "isctx G". *)
    - destruct (trans_ctx _ H) as [G' HGisG'].
      destruct (trans_type G G' A i HGisG') as [A' [pp qq]].
      admit.
  }
  (****** trans_substl ******)
  - { induction H.

    (* SubstZero *)
    + admit.

    (* SubstWeak *)
    + admit.

    (* SubstShift *)
    + admit.
  }
  (****** trans_substr ******)
  - {  induction H.

    (* SubstZero *)
    + admit.

    (* SubstWeak *)
    + admit.

    (* SubstShift *)
    + admit.
  }
Abort.
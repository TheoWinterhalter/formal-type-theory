Require ett.
Require ctt.

Module E := ett.
Module C := ctt.

(* "hom" stands for "homologous" which is too long to type. *)

Inductive hom_context :
  E.context -> C.context -> Type :=

  | hom_ctxempty :
      hom_context E.ctxempty C.ctxempty

  | hom_ctxextend : 
      forall {G G' A A'}, 
        hom_context G G' ->
        hom_type A A' ->
        hom_context (E.ctxextend G A) (C.ctxextend G' A')

with hom_type :
 E.type -> C.type -> Type :=
       
 | hom_Id :
     forall {A A' u u' v v' c},
       hom_type A A' ->
       hom_term u u' ->
       hom_term v v' ->
       hom_type (E.Id A u v) (C.Coerce c (C.Id A' u' v'))

with hom_term : 
  E.term -> C.term -> Type :=

 | hom_var {k c1 c2} :
     hom_term (E.var k) (C.coerce c1 c2 (C.var k))
.

Structure istrans_ctx (G : E.context) (G' : C.context) :=
  { 
    isctx_derive : C.isctx G' ;
    isctx_hom : hom_context G G'
  }.

Structure istrans_type (A : E.type) (G' : C.context) (A' : C.type) :=
  { 
    istype_derive : C.istype G' A' ;
    istype_hom : hom_type A A'
  }.

Structure istrans_term (u : E.term) (G' : C.context) (A' : C.type) (u' : C.term) :=
  {
    isterm_derive : C.isterm G' u' A' ;
    isterm_hom : hom_term u u'
  }.

Inductive equiv_type : C.type -> C.type -> Type :=.

Fixpoint trans_ctx {G} (H : E.isctx G) {struct H} :
  { G' : C.context & istrans_ctx G G' }

with trans_substl {G G' D sbs} (H : E.issubst sbs G D)
                  (Ht : istrans_ctx G G') {struct H} :
       { D' : C.context & { sbt : C.substitution & C.issubst sbt G' D' } }

with trans_substr {G D D' sbs} (H : E.issubst sbs G D)
                  (Ht : istrans_ctx D D') {struct H} :
       { G' : C.context & { sbt : C.substitution & C.issubst sbt G' D' } }

with trans_type {G G' A} (H : E.istype G A) (Ht : istrans_ctx G G') {struct H} :
       { A' : C.type & istrans_type A G' A' }

with trans_type2 {G A G' A''} (H : E.istype G A) (Ht : istrans_ctx G G')
                 (Hty : istrans_type A G' A'') {struct H} :
       { A' : C.type & (istrans_type A G' A' * equiv_type A' A'')%type }.
Proof.
  (****** trans_ctx ******)
  - induction H.

    (* CtxEmpty *)
    + admit.

    (* CtxExtend *)
    + (* We cannot win without sanity... *)
      admit.

  (****** trans_substl ******)
  - induction H.

    (* SubstZero *)
    + admit.

    (* SubstWeak *)
    + admit.

    (* SubstShift *)
    + admit.

  (****** trans_substr ******)
  - induction H.

    (* SubstZero *)
    + admit.

    (* SubstWeak *)
    + admit.

    (* SubstShift *)
    + admit.

Abort.
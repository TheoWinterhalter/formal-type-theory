Require Import ett.

Open Scope type_scope.

Module Dummy : Param.
End Dummy.

Module S := Theory (Dummy).
Module T := Theory (Dummy).

Inductive same_shape_ctx : S.context -> T.context -> Type :=
| same_shape_ctx_empty : same_shape_ctx S.ctxempty T.ctxempty.

Inductive same_shape_type : S.type -> T.type -> Type :=.

Definition istrans_ctx D G :=
  T.isctx D * same_shape_ctx G D.

Definition istrans_type G' A' A :=
  T.istype G' A' * same_shape_type A A'.

Inductive equiv_type : T.type -> T.type -> Type :=.

Fixpoint trans_ctx {G} (H : S.isctx G) {struct H} :
  { D : T.context & istrans_ctx D G }

with trans_substl {G G' D sbs} (H : S.issubst sbs G D)
                  (Ht : istrans_ctx G' G) {struct H} :
       { D' : T.context & { sbt : T.substitution & T.issubst sbt G' D' } }

with trans_substr {G D D' sbs} (H : S.issubst sbs G D)
                  (Ht : istrans_ctx D' D) {struct H} :
       { G' : T.context & { sbt : T.substitution & T.issubst sbt G' D' } }

with trans_type {G G' A} (H : S.istype G A) (Ht : istrans_ctx G' G) {struct H} :
       { A' : T.type & istrans_type G' A' A }

with trans_type2 {G G' A A''} (H : S.istype G A) (Ht : istrans_ctx G' G)
                 (Hty : istrans_type G' A'' A) {struct H} :
       { A' : T.type & istrans_type G' A' A * equiv_type A' A'' }.
Proof.
  (****** trans_ctx ******)
  - induction H.

    (* CtxEmpty *)
    + exists T.ctxempty. split.
      * constructor.
      * constructor.

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
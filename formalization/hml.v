Require Import syntax.
Require ctt.

(* "hml" stands for "homologous" which is too long to type. *)

Inductive hml_context :
  context -> ctt.context -> Type :=

  | hml_ctxempty :
      hml_context ctxempty ctt.ctxempty

  | hml_ctxextend :
      forall {G G' A A'},
        hml_context G G' ->
        hml_type A A' ->
        hml_context (ctxextend G A) (ctt.ctxextend G' A')

with hml_substitution :
  substitution -> ctt.substitution -> Type :=

  | hml_sbzero :
      forall {A A' u u' c},
        hml_type A A' ->
        hml_term u u' ->
        hml_substitution (sbzero A u) (ctt.sbcoerce c (ctt.sbzero A' u'))

  | hml_sbweak :
      forall {A A' c},
        hml_type A A' ->
        hml_substitution (sbweak A) (ctt.sbcoerce c (ctt.sbweak A'))

  | hml_sbshift :
      forall {A A' sbs sbs' c},
        hml_type A A' ->
        hml_substitution sbs sbs' ->
        hml_substitution (sbshift A sbs)
                         (ctt.sbcoerce c (ctt.sbshift A' sbs'))

  | hml_sbid :
      forall {c},
        hml_substitution sbid (ctt.sbcoerce c ctt.sbid)

  | hml_sbcomp :
      forall {sbs sbs' sbt sbt' c},
        hml_substitution sbs sbs' ->
        hml_substitution sbt sbt' ->
        hml_substitution (sbcomp sbs sbt)
                         (ctt.sbcoerce c (ctt.sbcomp sbs' sbt'))

with hml_type :
  type -> ctt.type -> Type :=

  | hml_Prod :
      forall {A A' B B' c},
        hml_type A A' ->
        hml_type B B' ->
        hml_type (Prod A B) (ctt.Coerce c (ctt.Prod A' B'))

  | hml_Id :
      forall {A A' u u' v v' c},
        hml_type A A' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_type (Id A u v) (ctt.Coerce c (ctt.Id A' u' v'))

  | hml_Subst :
      forall {A A' sbs sbs' c},
        hml_type A A' ->
        hml_substitution sbs sbs' ->
        hml_type (Subst A sbs) (ctt.Coerce c (ctt.Subst A' sbs'))

  | hml_Empty :
      forall {c},
        hml_type Empty (ctt.Coerce c ctt.Empty)

  | hml_Unit :
      forall {c},
        hml_type Unit (ctt.Coerce c ctt.Unit)

  | hml_Bool :
      forall {c},
        hml_type Bool (ctt.Coerce c ctt.Bool)

with hml_term :
  term -> ctt.term -> Type :=

  | hml_var {k c} :
      hml_term (var k) (ctt.coerce c (ctt.var k))

  | hml_lam :
      forall {A A' B B' u u' c},
        hml_type A A' ->
        hml_type B B' ->
        hml_term u u' ->
        hml_term (lam A B u) (ctt.coerce c (ctt.lam A' B' u'))

  | hml_app :
      forall {A A' B B' u u' v v' c},
        hml_type A A' ->
        hml_type B B' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_term (app u A B v)
                 (ctt.coerce c (ctt.app u' A' B' v'))

  | hml_refl :
      forall {A A' u u' c},
        hml_type A A' ->
        hml_term u u' ->
        hml_term (refl A u) (ctt.coerce c (ctt.refl A' u'))

  | hml_j :
      forall {A A' C C' u u' v v' w w' p p' c},
        hml_type A A' ->
        hml_type C C' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_term w w' ->
        hml_term p p' ->
        hml_term (j A u C w v p)
                 (ctt.coerce c (ctt.j A' u' C' w' v' p'))

  | hml_subst :
      forall {u u' sbs sbs' c},
        hml_term u u' ->
        hml_substitution sbs sbs' ->
        hml_term (subst u sbs)
                 (ctt.coerce c (ctt.subst u' sbs'))

  | hml_exfalso :
      forall {A A' u u' c},
        hml_type A A' ->
        hml_term u u' ->
        hml_term (exfalso A u) (ctt.coerce c (ctt.exfalso A' u'))

  | hml_unit :
      forall {c},
        hml_term unit (ctt.coerce c ctt.unit)

  | hml_true :
      forall {c},
        hml_term true (ctt.coerce c ctt.true)

  | hml_false :
      forall {c},
        hml_term false (ctt.coerce c ctt.false)

  | hml_cond :
      forall {C C' u u' v v' w w' c},
        hml_type C C' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_term w w' ->
        hml_term (cond C u v w)
                 (ctt.coerce c (ctt.cond C' u' v' w'))

.

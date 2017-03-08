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
      forall {A A' u u'},
        hml_type A A' ->
        hml_term u u' ->
        hml_substitution (sbzero A u) (ctt.sbzero A' u')

  | hml_sbweak :
      forall {A A'},
        hml_type A A' ->
        hml_substitution (sbweak A) (ctt.sbweak A')

  | hml_sbshift :
      forall {A A' sbs sbs'},
        hml_type A A' ->
        hml_substitution sbs sbs' ->
        hml_substitution (sbshift A sbs)
                         (ctt.sbshift A' sbs')

  | hml_sbid :
        hml_substitution sbid ctt.sbid

  | hml_sbcomp :
      forall {sbs sbs' sbt sbt'},
        hml_substitution sbs sbs' ->
        hml_substitution sbt sbt' ->
        hml_substitution (sbcomp sbs sbt)
                         (ctt.sbcomp sbs' sbt')

  | hml_sbcoerce :
      forall {sbs sbs' G G' D D'}
             {crc1 : ctt.context_coercion G G'}
             {crc2 : ctt.context_coercion D D'},
        hml_substitution sbs sbs' ->
        hml_substitution sbs (ctt.sbcoerce crc1 crc2 sbs')


with hml_type :
  type -> ctt.type -> Type :=

  | hml_Prod :
      forall {A A' B B'},
        hml_type A A' ->
        hml_type B B' ->
        hml_type (Prod A B) (ctt.Prod A' B')

  | hml_Id :
      forall {A A' u u' v v'},
        hml_type A A' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_type (Id A u v) (ctt.Id A' u' v')

  | hml_Subst :
      forall {A A' sbs sbs'},
        hml_type A A' ->
        hml_substitution sbs sbs' ->
        hml_type (Subst A sbs) (ctt.Subst A' sbs')

  | hml_Empty :
        hml_type Empty ctt.Empty

  | hml_Unit :
        hml_type Unit ctt.Unit

  | hml_Bool :
        hml_type Bool ctt.Bool

  | hml_Coerce :
      forall {A A' G G'} {crc : ctt.context_coercion G G'},
        hml_type A A' ->
        hml_type A (ctt.Coerce crc A')

with hml_term :
  term -> ctt.term -> Type :=

  | hml_var {k} :
      hml_term (var k) (ctt.var k)

  | hml_lam :
      forall {A A' B B' u u'},
        hml_type A A' ->
        hml_type B B' ->
        hml_term u u' ->
        hml_term (lam A B u) (ctt.lam A' B' u')

  | hml_app :
      forall {A A' B B' u u' v v'},
        hml_type A A' ->
        hml_type B B' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_term (app u A B v)
                 (ctt.app u' A' B' v')

  | hml_refl :
      forall {A A' u u'},
        hml_type A A' ->
        hml_term u u' ->
        hml_term (refl A u) (ctt.refl A' u')

  | hml_j :
      forall {A A' C C' u u' v v' w w' p p'},
        hml_type A A' ->
        hml_type C C' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_term w w' ->
        hml_term p p' ->
        hml_term (j A u C w v p)
                 (ctt.j A' u' C' w' v' p')

  | hml_subst :
      forall {u u' sbs sbs'},
        hml_term u u' ->
        hml_substitution sbs sbs' ->
        hml_term (subst u sbs)
                 (ctt.subst u' sbs')

  | hml_exfalso :
      forall {A A' u u'},
        hml_type A A' ->
        hml_term u u' ->
        hml_term (exfalso A u) (ctt.exfalso A' u')

  | hml_unit :
        hml_term unit ctt.unit

  | hml_true :
        hml_term true ctt.true

  | hml_false :
        hml_term false ctt.false

  | hml_cond :
      forall {C C' u u' v v' w w'},
        hml_type C C' ->
        hml_term u u' ->
        hml_term v v' ->
        hml_term w w' ->
        hml_term (cond C u v w)
                 (ctt.cond C' u' v' w')

  | hml_coerce :
      forall {u u' G G' A A'}
             {crc : ctt.context_coercion G G'}
             {crt : ctt.type_coercion crc A A'},
        hml_term u u' ->
        hml_term u (ctt.coerce crt u')
.

Require Import syntax.
Require ett ptt.
Require Import ptt_inversion.
Require ptt_sanity.
Require Import tactics.

(* We prove the inversion lemmata here before putting them in ptt_inversion *)
(* This will speed up the compilation process a bit. *)

Fixpoint TermAbsInversion {G A B u T} (H : ptt.isterm G (lam A B u) T) {struct H} :
  ptt.isctx G *
  ptt.istype G A *
  ptt.istype (ctxextend G A) B *
  ptt.isterm (ctxextend G A) u B *
  ptt.eqtype G (Prod A B) T.
Proof.
  inversion H.

  - { destruct (@TermAbsInversion _ _ _ _ _ H0) as [[[[? ?] ?] ?] ?].
      repeat split ; try assumption.
      eapply ptt.EqTyTrans ; [
        eassumption
      | try assumption ..
      ].
      eapply ptt.TyProd ; assumption.
    }

  - { destruct (@TermAbsInversion _ _ _ _ _ H0) as [[[[? ?] ?] ?] ?].
      assert (ptt.eqctx (ctxextend G0 A) (ctxextend G A)).
      { eapply ptt.EqCtxExtend ; try assumption.
        eapply ptt.EqTyRefl ; assumption.
      }
      assert (ptt.isctx (ctxextend G0 A)).
      { eapply ptt.CtxExtend ; assumption. }
      assert (ptt.isctx (ctxextend G A)).
      { eapply ptt.CtxExtend ; try assumption.
        eapply ptt.TyCtxConv ; eassumption.
      }
      repeat split.
      - assumption.
      - eapply ptt.TyCtxConv ; eassumption.
      - eapply ptt.TyCtxConv ; eassumption.
      - eapply ptt.TermCtxConv ; eassumption.
      - eapply ptt.EqTyCtxConv ; try eassumption.
        eapply ptt.TyProd ; assumption.
    }

  - { repeat split ; try assumption.
      apply ptt.EqTyRefl ; try assumption.
      apply ptt.TyProd ; assumption.
    }

Defined.

Fixpoint TermAppInversion {G A B u v T}
         (H : ptt.isterm G (app u A B v) T) {struct H} :
  ptt.isctx G *
  ptt.istype G A *
  ptt.istype (ctxextend G A) B *
  ptt.isterm G u (Prod A B) *
  ptt.isterm G v A *
  ptt.eqtype G (Subst B (sbzero G A v)) T.
Proof.
  inversion H.

  - { destruct (@TermAppInversion _ _ _ _ _ _ H0) as [[[[[? ?] ?] ?] ?] ?].
      repeat split ; try assumption.
      eapply ptt.EqTyTrans ; [
        eassumption
      | try assumption ..
      ].
      eapply ptt.TySubst ; try eassumption.
      - eapply ptt.SubstZero ; eassumption.
      - eapply ptt.CtxExtend ; assumption.
    }

  - { destruct (@TermAppInversion _ _ _ _ _ _ H0) as [[[[[? ?] ?] ?] ?] ?].
      assert (ptt.eqctx (ctxextend G0 A) (ctxextend G A)).
      { eapply ptt.EqCtxExtend ; try assumption.
        eapply ptt.EqTyRefl ; assumption.
      }
      assert (ptt.isctx (ctxextend G0 A)).
      { eapply ptt.CtxExtend ; assumption. }
      assert (ptt.isctx (ctxextend G A)).
      { eapply ptt.CtxExtend ; try assumption.
        eapply ptt.TyCtxConv ; eassumption.
      }
      repeat split.
      - assumption.
      - eapply ptt.TyCtxConv ; eassumption.
      - eapply ptt.TyCtxConv ; eassumption.
      - eapply ptt.TermCtxConv ; try eassumption.
        eapply ptt.TyCtxConv ; [
          eapply ptt.TyProd ; eassumption
        | try eassumption ..
        ].
        apply ptt.CtxRefl ; assumption.
      - eapply ptt.TermCtxConv ; try eassumption.
      - eapply ptt.EqTyCtxConv ; try eassumption.
        + eapply ptt.EqTyTrans ; try eassumption.
          * { eapply ptt.CongTySubst ; try eassumption.
              - eapply ptt.EqSubstCtxConv ; [
                  eapply ptt.CongSubstZero ; try eassumption
                | try eassumption ..
                ].

Admitted.

Fixpoint TermReflInversion {G A u T}
         (H : ptt.isterm G (refl A u) T) {struct H} :
  ptt.isctx G *
  ptt.istype G A *
  ptt.isterm G u A *
  ptt.eqtype G (Id A u u) T.
Proof.
  inversion H.

  - { destruct (@TermReflInversion _ _ _ _ H0) as [[[? ?] ?] ?].
      repeat split ; try assumption.
      eapply ptt.EqTyTrans ; [
        eassumption
      | try assumption ..
      ].
      eapply ptt.TyId ; eassumption.
    }

  - admit.

  - admit.

Admitted.

Fixpoint TermJInversion {G A u C w v p T}
         (H : ptt.isterm G (j A u C w v p) T) {struct H} :
  ptt.isctx G *
  ptt.istype G A *
  ptt.isterm G u A *
  ptt.istype
    (ctxextend
       (ctxextend G A)
       (Id
          (Subst A (sbweak G A))
          (subst u (sbweak G A))
          (var 0)
       )
    )
    C *
  ptt.isterm G
             w
             (Subst
                (Subst
                   C
                   (sbshift
                      G
                      (Id
                         (Subst A (sbweak G A))
                         (subst u (sbweak G A))
                         (var 0)
                      )
                      (sbzero G A u)
                   )
                )
                (sbzero G (Id A u u) (refl A u))
             ) *
  ptt.isterm G v A *
  ptt.isterm G p (Id A u v) *
  ptt.eqtype G
             (Subst
                (Subst
                   C
                   (sbshift
                      G
                      (Id
                         (Subst A (sbweak G A))
                         (subst u (sbweak G A))
                         (var 0)
                      )
                      (sbzero G A v)
                   )
                )
                (sbzero G (Id A u v) p)
             )
             T.
Proof.
  inversion H.

  - { destruct (@TermJInversion _ _ _ _ _ _ _ _ H0)
        as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
      repeat split ; try assumption.
      eapply ptt.EqTyTrans ; [
        eassumption
      | try assumption ..
      ].
      admit.
    }

  - admit.

  - admit.

Admitted.

Fixpoint TermExfalsoInversion {G A u T}
         (H : ptt.isterm G (exfalso A u) T) {struct H} :
  ptt.isctx G *
  ptt.istype G A *
  ptt.isterm G u Empty *
  ptt.eqtype G A T.
Proof.
  inversion H.

  - { destruct (@TermExfalsoInversion _ _ _ _ H0) as [[[? ?] ?] ?].
      repeat split ; try assumption.
      eapply ptt.EqTyTrans ; [
        eassumption
      | try assumption ..
      ].
    }

  - admit.

  - admit.

Admitted.

Fixpoint TermCondInversion {G C u v w T}
         (H : ptt.isterm G (cond C u v w) T) {struct H} :
  ptt.isctx G *
  ptt.isterm G u Bool *
  ptt.istype (ctxextend G Bool) C *
  ptt.isterm G v (Subst C (sbzero G Bool true)) *
  ptt.isterm G w (Subst C (sbzero G Bool false)) *
  ptt.eqtype G (Subst C (sbzero G Bool u)) T.
Proof.
  inversion H.

  - { destruct (@TermCondInversion _ _ _ _ _ _ H0) as [[[[[? ?] ?] ?] ?] ?].
      repeat split ; try assumption.
      eapply ptt.EqTyTrans ; [
        eassumption
      | try assumption ..
      ].
      eapply ptt.TySubst ; try eassumption.
      - admit.
      - eapply ptt.CtxExtend ; try eassumption.
        eapply ptt.TyBool. assumption.
    }

  - admit.

  - admit.

Admitted.


Inductive subst_free_term : term -> Type :=
  | subst_free_var :
      forall n,
        subst_free_term (var n)

  | subst_free_lam :
      forall A B u,
        subst_free_type A ->
        subst_free_type B ->
        subst_free_term u ->
        subst_free_term (lam A B u)

  | subst_free_app :
      forall u A B v,
        subst_free_term u ->
        subst_free_type A ->
        subst_free_type B ->
        subst_free_term v ->
        subst_free_term (app u A B v)

  | subst_free_refl :
      forall A u,
        subst_free_type A ->
        subst_free_term u ->
        subst_free_term (refl A u)

  | subst_free_j :
      forall A u C w v p,
        subst_free_type A ->
        subst_free_term u ->
        subst_free_type C ->
        subst_free_term w ->
        subst_free_term v ->
        subst_free_term p ->
        subst_free_term (j A u C w v p)

  (* NB: subst is not subst free! *)

  | subst_free_exfalso :
      forall A u,
        subst_free_type A ->
        subst_free_term u ->
        subst_free_term (exfalso A u)

  | subst_free_unit :
      subst_free_term unit

  | subst_free_true :
      subst_free_term true

  | subst_free_false :
      subst_free_term false

  | subst_free_cond :
      forall A u v w,
        subst_free_type A ->
        subst_free_term u ->
        subst_free_term v ->
        subst_free_term w ->
        subst_free_term (cond A u v w)

with subst_free_type : type -> Type :=

  | subst_free_Prod :
      forall A B,
        subst_free_type A ->
        subst_free_type B ->
        subst_free_type (Prod A B)

  | subst_free_Id :
      forall A u v,
        subst_free_type A ->
        subst_free_term u ->
        subst_free_term v ->
        subst_free_type (Id A u v)

  (* NB: Subst is not subst free! *)

  | subst_free_Empty :
      subst_free_type Empty

  | subst_free_Unit :
      subst_free_type Unit

  | subst_free_Bool :
      subst_free_type Bool
.

Hypothesis temporary : forall {A}, A.
Ltac todo := exact temporary.

(* In order to apply substitution to a term, we use substitutions
   without annotations. *)
Inductive meta_subst :=
| msbzero  : term -> meta_subst
| msbweak  : meta_subst
| msbshift : meta_subst -> meta_subst
| msbid    : meta_subst
| msbcomp  : meta_subst -> meta_subst -> meta_subst.

Fixpoint erase_subst (sbs : substitution) : meta_subst :=
  match sbs with
  | sbzero G A u    => msbzero u
  | sbweak G A      => msbweak
  | sbshift G A sbs => msbshift (erase_subst sbs)
  | sbid G          => msbid
  | sbcomp sbs sbt  => msbcomp (erase_subst sbs) (erase_subst sbt)
  end.

(* Apply a meta_subst to a variable. *)
Fixpoint apply_meta_subst_var (n : nat) (sbs : meta_subst) {struct sbs} : term :=
  match sbs with
  | msbzero u =>
    match n with
    | 0 => u
    | S k => var k
    end
  | msbweak => var (S n)
  | msbshift sbs =>
    match n with
    | 0 => temporary (* This case can't happen so we probably
                       need more hypotheses or be sure to deal with outside. *)
    | S k => var k
    end
  | msbid => var n
  | msbcomp sbt sbs =>
    apply_meta_subst (apply_meta_subst_var n sbt) sbs
  end

(* Temporarily we don't prove anything about typing. *)
with apply_meta_subst (u : term) (sbs : meta_subst) {struct u} : term :=
  match u with
  | var n => apply_meta_subst_var n sbs
  | lam A B u =>
    let A' := apply_meta_Subst A sbs in
    let B' := apply_meta_Subst B (msbshift sbs) in
    let u' := apply_meta_subst u (msbshift sbs) in
    lam A' B' u'
  | app u A B v =>
    let u' := apply_meta_subst u sbs in
    let A' := apply_meta_Subst A sbs in
    let B' := apply_meta_Subst B (msbshift sbs) in
    let v' := apply_meta_subst v sbs in
    app u' A' B' v'
  | refl A u =>
    let A' := apply_meta_Subst A sbs in
    let u' := apply_meta_subst u sbs in
    refl A' u'
  | j A u C w v p =>
    let A' := apply_meta_Subst A sbs in
    let u' := apply_meta_subst u sbs in
    let C' := apply_meta_Subst C (msbshift (msbshift sbs)) in
    let w' := apply_meta_subst w sbs in
    let v' := apply_meta_subst v sbs in
    let p' := apply_meta_subst p sbs in
    j A' u' C' w' v' p'
  | subst u sbt =>
    apply_meta_subst u (msbcomp (erase_subst sbt) sbs)
  | exfalso A u =>
    let A' := apply_meta_Subst A sbs in
    let u' := apply_meta_subst u sbs in
    exfalso A' u'
  | unit => unit
  | true => true
  | false => false
  | cond C u v w =>
    let C' := apply_meta_Subst C (msbshift sbs) in
    let u' := apply_meta_subst u sbs in
    let v' := apply_meta_subst v sbs in
    let w' := apply_meta_subst w sbs in
    cond C' u' v' w'
  end

with apply_meta_Subst (A : type) (sbs : meta_subst) {struct A} : type :=
  match A with
  | Prod A B =>
    let A' := apply_meta_Subst A sbs in
    let B' := apply_meta_Subst B (msbshift sbs) in
    Prod A' B'
  | Id A u v =>
    let A' := apply_meta_Subst A sbs in
    let u' := apply_meta_subst u sbs in
    let v' := apply_meta_subst v sbs in
    Id A' u' v'
  | Subst A sbt =>
    apply_meta_Subst A (msbcomp (erase_subst sbt) sbs)
  | Empty => Empty
  | Unit => Unit
  | Bool => Bool
  end.

(* Fixpoint apply_subst u sbs {struct u} : *)
(*   { v : term & *)
(*     subst_free_term v * *)
(*     (forall G A, ptt.isterm G (subst u sbs) A -> ett.eqterm G (subst u sbs) v A) *)
(*   }%type *)

(* with apply_Subst A sbs {struct A} : *)
(*   { B : type & *)
(*     subst_free_type B * *)
(*     (forall G, ptt.istype G (Subst A sbs) -> ett.eqtype G (Subst A sbs) B) *)
(*   }%type. *)
(* Proof. *)
(*   (* apply_subst *) *)
(*   - { simple refine ( *)
(*         match u with *)
(*         | var n => existT _ temporary _ *)

(*         | lam A B u => *)
(*           let [A' hA] := apply_Subst A sbs in *)
(*           let [B' hB] := apply_Susbt B (sbshift _ A sbs) in *)
(*           let [u' hu] := apply_subst u (sbshift _ A sbs) in *)
(*           existT _ (lam A' B' u') _ *)

(*         | app u A B v => *)
(*           let [u' hu] := apply_subst u sbs in *)
(*           let [A' hA] := apply_subst A sbs in *)
(*           let [B' hB] := apply_Subst B (sbshift _ A sbs) in *)
(*           let [v' hv] := apply_subst v sbs in *)
(*           existT _ (app u' A' B' v') _ *)
(*                  _ *)
(*         | refl A u => *)
(*           existT _ *)
(*                  (refl (Subst A sbs) (subst u sbs)) *)
(*                  _ *)
(*         | j A u C w v p => *)
(*           existT _ *)
(*                  (j (Subst A sbs) *)
(*                     (subst u sbs) *)
(*                     (Subst C *)
(*                            (sbshift *)
(*                               (ctxextend _ *)
(*                                          (Subst A sbs)) *)
(*                               (Id *)
(*                                  (Subst A (sbweak _ A)) *)
(*                                  (subst u (sbweak _ A)) *)
(*                                  (var 0) *)
(*                               ) *)
(*                               (sbshift _ A sbs) *)
(*                            ) *)
(*                     ) *)
(*                     (subst w sbs) *)
(*                     (subst v sbs) *)
(*                     (subst p sbs) *)
(*                  ) *)
(*                  _ *)
(*         | subst u sbt => existT _ (subst u (sbcomp sbt sbs)) _ *)
(*         | exfalso A u => *)
(*           existT _ *)
(*                  (exfalso (Subst A sbs) (subst u sbs)) *)
(*                  _ *)
(*         | unit => existT _ unit _ *)
(*         | true => existT _ true _ *)
(*         | false => existT _ false _ *)
(*         | cond C u v w => *)
(*           existT _ *)
(*                  (cond (Subst C (sbshift _ Bool sbs)) *)
(*                        (subst u sbs) *)
(*                        (subst v sbs) *)
(*                        (subst w sbs)) *)
(*                  _ *)
(*         end *)
(*       ). *)

(*       (* var *) *)
(*       - todo. *)

(*       (* We can't guess the contexts... *) *)
(*       - todo. *)
(*       - todo. *)

(*       (* lam *) *)
(*       - { split. *)
(*           - todo. *)
(*           - todo. *)
(*         } *)

(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*       - todo. *)
(*     } *)

(*   - { todo. } *)

(* Admitted. *)

(* A tactic to handle most elim cases. *)

(* Ltac auto_elim elim_term elim_type terms types (* inv *) := *)
(*   (* First we elim subst in every argument. *) *)
(*   let rec elim_terms terms := *)
(*       match terms with *)
(*       | nil => idtac *)
(*       | cons ?u ?l => destruct (elim_term u) as [? [? ?]] ; *)
(*                      elim_terms l *)
(*       | _ => fail *)
(*       end *)
(*   in elim_terms terms ; *)
(*   let rec elim_types types := *)
(*       match types with *)
(*       | nil => idtac *)
(*       | cons ?A ?l => destruct (elim_type A) as [? [? ?]] ; *)
(*                      elim_types l *)
(*       end *)
(*   in elim_types types. *)

Fixpoint elim_term u :
  { v : term &
    subst_free_term v *
    (forall G A, ptt.isterm G u A -> ett.eqterm G u v A)
  }%type

with elim_type A :
  { B : type &
    subst_free_type B *
    (forall G, ptt.istype G A -> ett.eqtype G A B)
  }%type.

Proof.
  (* elim_term *)
  - { destruct u.

      (* var *)
      - exists (var n). split.
        + constructor.
        + intros G A H.
          apply ett.EqRefl.
          hyp.

      (* lam *)
      - { (* auto_elim elim_term elim_type cons(u,nil) cons(t,cons(t0,nil)). *)
          destruct (elim_type t) as [A [sA fA]].
          destruct (elim_type t0) as [B [sB fB]].
          destruct (elim_term u) as [v [sv fv]].
          exists (lam A B v). split.
          - now constructor.
          - intros G T h.
            destruct (ptt_sanity.sane_isterm G (lam t t0 u) T h).
            destruct (TermAbsInversion h) as [[[[? ?] ?] ?] ?].
            eapply ett.EqTyConv.
            + eapply ett.CongAbs.
              * now apply fA.
              * now apply fB.
              * now apply fv.
            + hyp.
        }

      (* app *)
      - { destruct (elim_term u1) as [v1 [sv1 fv1]].
          destruct (elim_type t) as [A [sA fA]].
          destruct (elim_type t0) as [B [sB fB]].
          destruct (elim_term u2) as [v2 [sv2 fv2]].
          exists (app v1 A B v2). split.
          - now constructor.
          - intros G T h.
            destruct (TermAppInversion h) as [[[[[? ?] ?] ?] ?] ?].
            eapply ett.EqTyConv.
            + eapply ett.CongApp.
              * now apply fA.
              * now apply fB.
              * now apply fv1.
              * now apply fv2.
            + hyp.
        }

      (* refl *)
      - { destruct (elim_type t) as [A [sA fA]].
          destruct (elim_term u) as [v [sv fv]].
          exists (refl A v). split.
          - now constructor.
          - intros G T h.
            destruct (TermReflInversion h) as [[[? ?] ?] ?].
            eapply ett.EqTyConv.
            + eapply ett.CongRefl.
              * now apply fv.
              * now apply fA.
            + hyp.
        }

      (* j *)
      - { destruct (elim_type t) as [? [? ?]].
          destruct (elim_term u1) as [? [? ?]].
          destruct (elim_type t0) as [? [? ?]].
          destruct (elim_term u2) as [? [? ?]].
          destruct (elim_term u3) as [? [? ?]].
          destruct (elim_term u4) as [? [? ?]].
          exists (j x x0 x1 x2 x3 x4). split.
          - now constructor.
          - intros G T h.
            destruct (TermJInversion h) as [[[[[[[? ?] ?] ?] ?] ?] ?] ?].
            eapply ett.EqTyConv.
            + eapply ett.CongJ.
              * now apply e.
              * now apply e0.
              * now apply e1.
              * now apply e2.
              * now apply e3.
              * now apply e4.
            + hyp.
        }

      (* subst *)
      - (* What would we do here? Go though another destruction of u?
         When does it end? *)
        todo.

      (* exfalso *)
      - { destruct (elim_type t) as [? [? ?]].
          destruct (elim_term u) as [? [? ?]].
          exists (exfalso x x0). split.
          - now constructor.
          - intros G T h.
            destruct (TermExfalsoInversion h) as [[[? ?] ?] ?].
            pose proof (e _ i0).
            pose proof (e0 _ _ i1).

            eapply ett.EqTyConv.
            + eapply ett.EqTermExfalso.
              * eapply ett.TermExfalso ; hyp.
              * { eapply ett.TermTyConv.
                  - eapply ett.TermExfalso ; ett_sane.
                  - now apply ett.EqTySym.
                }
              * ehyp.
            + hyp.
        }

      (* unit *)
      - { exists unit. split.
          - now constructor.
          - intros G A h. constructor. hyp.
        }

      (* true *)
      - { exists true. split.
          - now constructor.
          - intros G A h. constructor. hyp.
        }

      (* false *)
      - { exists false. split.
          - now constructor.
          - intros G A h. constructor. hyp.
        }

      (* cond *)
      - { destruct (elim_type t) as [A [sA fA]].
          destruct (elim_term u1) as [v1 [sv1 fv1]].
          destruct (elim_term u2) as [v2 [sv2 fv2]].
          destruct (elim_term u3) as [v3 [sv3 fv3]].
          exists (cond A v1 v2 v3). split.
          - now constructor.
          - intros G T h.
            destruct (TermCondInversion h) as [[[[[? ?] ?] ?] ?] ?].
            pose proof (fA _ i1).
            pose proof (fv1 _ _ i0).
            pose proof (fv2 _ _ i2).
            pose proof (fv3 _ _ i3).

            eapply ett.EqTyConv.
            + eapply ett.CongCond ; assumption.
            + hyp.
        }
    }

  (* elim_type *)
  - { todo. }

Defined.

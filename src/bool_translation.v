(* We attempt a formalisation that goes from reflection for dSet to
   definitional UIP dSet using only Bool as dSet.
*)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.
Require Import checking_tactics.

Require Import Coq.Program.Equality.

Require Import Coq.Lists.List.

(* Source type theory *)
Module Stt.

  Section Stt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.Yes |}.
  Local Instance hasReflection : config.Reflection
    := {| config.reflectionFlag := config.No |}.
  Local Instance hasSimpleProducts : config.SimpleProducts
    := {| config.simpleproductsFlag := config.No |}.
  Local Instance hasProdEta : config.ProdEta
    := {| config.prodetaFlag := config.No |}.
  Local Instance hasUniverses : config.Universes
    := {| config.universesFlag := config.No |}.
  Local Instance hasProp : config.WithProp
    := {| config.withpropFlag := config.No |}.
  Local Instance hasJ : config.WithJ
    := {| config.withjFlag := config.No |}.
  Local Instance hasEmpty : config.WithEmpty
    := {| config.withemptyFlag := config.No |}.
  Local Instance hasUnit : config.WithUnit
    := {| config.withunitFlag := config.No |}.
  Local Instance hasBool : config.WithBool
    := {| config.withboolFlag := config.Yes |}.
  Local Instance hasBoolReflection : config.BoolReflection
    := {| config.boolreflectionFlag := config.Yes |}.
  Local Instance hasBoolUIP : config.BoolUIP
    := {| config.booluipFlag := config.No |}.

  Definition isctx   := isctx.
  Definition issubst := issubst.
  Definition istype  := istype.
  Definition isterm  := isterm.
  Definition eqctx   := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype  := eqtype.
  Definition eqterm  := eqterm.

  End Stt.

End Stt.

(* Target type theory *)
Module Ttt.

  Section Ttt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.No |}.
  Local Instance hasReflection : config.Reflection
    := {| config.reflectionFlag := config.No |}.
  Local Instance hasSimpleProducts : config.SimpleProducts
    := {| config.simpleproductsFlag := config.No |}.
  Local Instance hasProdEta : config.ProdEta
    := {| config.prodetaFlag := config.No |}.
  Local Instance hasUniverses : config.Universes
    := {| config.universesFlag := config.No |}.
  Local Instance hasProp : config.WithProp
    := {| config.withpropFlag := config.No |}.
  Local Instance hasJ : config.WithJ
    := {| config.withjFlag := config.No |}.
  Local Instance hasEmpty : config.WithEmpty
    := {| config.withemptyFlag := config.No |}.
  Local Instance hasUnit : config.WithUnit
    := {| config.withunitFlag := config.No |}.
  Local Instance hasBool : config.WithBool
    := {| config.withboolFlag := config.Yes |}.
  Local Instance hasBoolReflection : config.BoolReflection
    := {| config.boolreflectionFlag := config.No |}.
  Local Instance hasBoolUIP : config.BoolUIP
    := {| config.booluipFlag := config.Yes |}.

  Definition isctx   := isctx.
  Definition issubst := issubst.
  Definition istype  := istype.
  Definition isterm  := isterm.
  Definition eqctx   := eqctx.
  Definition eqsubst := eqsubst.
  Definition eqtype  := eqtype.
  Definition eqterm  := eqterm.

  End Ttt.

End Ttt.

Section Translation.

Open Scope type_scope.
Open Scope list_scope.

Axiom admit : forall {A}, A.
Tactic Notation "admit" := (exact admit).

(* The main idea is that we translate types as types with holes for the
   dSets inhabitants together with the inhabitants that fill them.
   This way, two translations of the same type only diverge in what fills the
   holes.
   Terms are translated in a similar way.
   However, the definitional equalities are translated into propositional
   equalities between the Σ-types inhabitants that are produced.

   Note: The main idea is that being a dSet is a syntactic criterion,
   which allows us to place the holes without fail and thus make sure
   the rest of the strucuture doesn't have reflection, while eveything
   filling the holes verifies some definitional UIP in the target.

   We use Bool as the only dSet to examplify this for something that would
   ideally be a dSet (we would also like things like nat and other natural
   inductive types).

   This probably means that beside istran_*, the trans_* theorem is also
   wrongly stated.
   Question: Do we need to internalise Σ-types in order to do that? Or is there
   hope we can actually have the telescopes on the meta-level.
   This would also allow us to avoid all sorts of proofs of equality to
   write (and type check!) about them.
 *)

Inductive teletype : nat -> Type :=
| teletype_one (A : type) : teletype 0
| teletype_cons
    (d : term) (D : type) {n} (f : term -> teletype n) : teletype (S n)
.

Inductive teleterm : nat -> Type :=
| teleterm_one (u : term) : teleterm 0
| teleterm_cons
    (d : term) (D : type) {n} (f : term -> teleterm n) : teleterm (S n)
.

Fixpoint tele_eqtype
  (Γ : context) {n} (T1 T2 : teletype n) : Type.
Proof.
  dependent destruction T1 ; dependent destruction T2.
  - exact (Ttt.eqtype Γ A A0).
  - exact (
      { p : term &
        Ttt.isterm Γ p (Id D d d0) *
        forall d', Ttt.isterm Γ d D -> tele_eqtype Γ _ (f d') (f0 d')
      }
    ).
Defined.

(* Fixpoint tele_eqtype *)
(*   (Γ : context) {l} (T1 T2 : teletype l) : Type := *)
(*   match T1, T2 with *)
(*   | teletype_one A1, teletype_one A2 => *)
(*     Ttt.eqtype Γ A1 A2 *)
(*   | teletype_cons d1 D1 F1, teletype_cons d2 D2 F2 => *)
(*     Ttt.eqtype Γ D1 D2 * *)
(*     { p : term & *)
(*       Ttt.isterm Γ p (Id D1 d1 d2) * *)
(*       forall d, Ttt.isterm Γ d D1 -> tele_eqtype Γ (F1 d) (F2 d) *)
(*     } *)
(*   | _, _ => False *)
(*   end. *)

Fixpoint tele_eqterm
  (Γ : context) {n} (t1 t2 : teleterm n) (T1 T2 : teletype n) : Type.
Proof.
  dependent destruction t1 ; dependent destruction t2 ;
  dependent destruction T1 ; dependent destruction T2.
  - exact (
      Ttt.eqtype Γ A A0 *
      { p : term & Ttt.isterm Γ p (Id A u u0) }
    ).
  - exact (
      (* The two equalities should probably be in the type as well! *)
      (* Maybe have some support : teletype -> term list *)
      Ttt.eqterm Γ d d1 D *
      Ttt.eqterm Γ d0 d2 D *
      { p : term &
        Ttt.isterm Γ p (Id D d d0) *
        forall d', Ttt.isterm Γ d D -> tele_eqterm Γ _ (f d') (f0 d') (f1 d') (f2 d')
      }
    ).
Defined.

(* Fixpoint tele_eqterm *)
(*   (Γ : context) (t1 t2 : teleterm) (T1 T2 : teletype) : Type := *)
(*   match t1, t2, T1, T2 with *)
(*   | teleterm_one u1, teleterm_one u2, teletype_one A1, teletype_one A2 => *)
(*     Ttt.eqtype Γ A1 A2 * *)
(*     { p : term & Ttt.isterm Γ p (Id A1 u1 u2) } *)
(*   | teleterm_cons d1 D1 f1, teleterm_cons d2 D2 f2, *)
(*     teletype_cons e1 E1 F1, teletype_cons e2 E2 F2 => *)
(*     Ttt.eqtype Γ D1 D2 * *)
(*     Ttt.eqtype Γ D1 E1 * *)
(*     Ttt.eqtype Γ D1 E2 * *)
(*     { p : term & *)
(*       Ttt.isterm Γ p (Id D1 d1 d2) * *)
(*       (* tele_eqterm Γ (f1 d1) (f2 d1) (F1 d1) (F2 d1) *) *)
(*       forall d, Ttt.isterm Γ d D1 -> tele_eqterm Γ (f1 d) (f2 d) (F1 d) (F2 d) *)
(*     } *)
(*   | _, _, _, _ => False *)
(*   end. *)

Fixpoint tele_to_type {n} (T : teletype n) : type :=
  match T with
  | teletype_one A => A
  | teletype_cons d D F => tele_to_type (F d)
  end.

Fixpoint tele_to_term {n} (t : teleterm n) : term :=
  match t with
  | teleterm_one u => u
  | teleterm_cons d D f => tele_to_term (f d)
  end.

(* Notion of transport based on tele_eqtype.

   TODO!
 *)

(* Notion of homology between expressions.

   This is some soundness safety in a way. We're making sure
   things get translated to similar things.

   TODO: We need first to know exactly how the translation affets
   terms: probably through transports that we wish to ignore when comparing
   an expression and its translation.
*)

Record contextᵗ (Γ : context) := mkctxᵗ {
  _context : context ;
  isctx    : Ttt.isctx _context
}.

Arguments _context {_} _.
Arguments isctx {_} _.
Coercion _context : contextᵗ >-> context.

Record substitutionᵗ
  {Γ} (Γᵗ : contextᵗ Γ) {Δ} (Δᵗ : contextᵗ Δ) (σ : substitution) := mksubstᵗ {
  _substitution : substitution ;
  issubst       : Ttt.issubst _substitution Γᵗ Δᵗ
}.

Arguments _substitution {_ _ _ _ _} _.
Arguments issubst {_ _ _ _ _} _.
Coercion _substitution : substitutionᵗ >-> substitution.

Record typeᵗ {Γ} (Γᵗ : contextᵗ Γ) (A : type) := mktypeᵗ {
  support   : nat ;
  _teletype : teletype support ;
  _type     := tele_to_type _teletype ;
  istype    : Ttt.istype Γᵗ _type
}.

Arguments support {_ _ _} _.
Arguments _teletype {_ _ _} _.
Arguments _type {_ _ _} _.
Arguments istype {_ _ _} _.
Coercion _type : typeᵗ >-> type.
Coercion _teletype : typeᵗ >-> teletype.

Record termᵗ {Γ} {Γᵗ : contextᵗ Γ} {A} (Aᵗ : typeᵗ Γᵗ A) (u : term) := mktermᵗ {
  _teleterm : teleterm (support Aᵗ) ;
  _term     := tele_to_term _teleterm ;
  isterm : Ttt.isterm Γᵗ _term Aᵗ
}.

Arguments _teleterm {_ _ _ _ _} _.
Arguments _term {_ _ _ _ _} _.
Arguments isterm {_ _ _ _ _} _.
Coercion _term : termᵗ >-> term.
Coercion _teleterm : termᵗ >-> teleterm.

Record eqctxᵗ {Γ} (Γᵗ : contextᵗ Γ) {Δ} (Δᵗ : contextᵗ Δ) := {
  (* TODO *)
}.

Record eqsubstᵗ
  {Γ} {Γᵗ : contextᵗ Γ} {Δ} {Δᵗ : contextᵗ Δ}
  {σ} (σᵗ : substitutionᵗ Γᵗ Δᵗ σ)
  {ρ} (ρᵗ : substitutionᵗ Γᵗ Δᵗ ρ)
  := {
  (* TODO *)
}.

(* We need to fix something here, probably! *)
Definition eqtypeᵗ
  {Γ} {Γᵗ : contextᵗ Γ}
  {A} (Aᵗ : typeᵗ Γᵗ A)
  {B} (Bᵗ : typeᵗ Γᵗ B)
  (* := tele_eqtype Γᵗ Aᵗ Bᵗ. *)
  := False.

Definition eqtermᵗ
  {Γ} {Γᵗ : contextᵗ Γ}
  {A} {Aᵗ : typeᵗ Γᵗ A}
  {u} (uᵗ : termᵗ Aᵗ u)
  {v} (vᵗ : termᵗ Aᵗ v)
  := tele_eqterm Γᵗ uᵗ vᵗ Aᵗ Aᵗ.

(* Note this is still not ok, we want to have telescopes and also
   constraints on the translation itself, like homology to the original
   perhaps. *)

(* Let's build meta constructors on translations *)
Definition ctxemptyᵗ : contextᵗ ctxempty.
Proof.
  exists ctxempty. capply CtxEmpty.
Defined.

Definition ctxextendᵗ {Γ} (Γᵗ : contextᵗ Γ) {A} (Aᵗ : typeᵗ Γᵗ A) :
  contextᵗ (ctxextend Γ A).
Proof.
  unshelve (eapply mkctxᵗ).
  - exact (ctxextend Γᵗ Aᵗ).
  - capply CtxExtend. apply (istype Aᵗ).
Defined.

Definition Idᵗ
  {Γ} {Γᵗ : contextᵗ Γ}
  {A} (Aᵗ : typeᵗ Γᵗ A)
  {u} (uᵗ : termᵗ Aᵗ u)
  {v} (vᵗ : termᵗ Aᵗ v)
  : typeᵗ Γᵗ (Id A u v).
Proof.
  unshelve (eapply mktypeᵗ).
  - destruct Aᵗ as [teleA tA isA].
    dependent induction teleA.
    + (* Here, I'd like to know that uᵗ and vᵗ have the same dependencies
         as Aᵗ, otherwise there will be cases in which I won't be able to
         conclude!
       *)
Abort.

(* One essential lemma that we want to have on translations is that
   two translations of the same term that live at the same type are
   definitionally equal. This relies on the definitional UIP present
   in the target type theory.

   We cannot prove it in the current state, but this should be around to
   guide the definition of termᵗ and typeᵗ.
*)
Lemma termᵗ_coh :
  forall {Γ} {Γᵗ : contextᵗ Γ}
    {A} {Aᵗ : typeᵗ Γᵗ A}
    {u} (uᵗ uᵗ' : termᵗ Aᵗ u),
    Ttt.eqterm Γᵗ uᵗ uᵗ' Aᵗ.
Admitted.

Fixpoint trans_isctx {Γ} (H : Stt.isctx Γ) {struct H} :
  contextᵗ Γ

with trans_issubst {Γ Δ σ} (H : Stt.issubst σ Γ Δ) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Δᵗ : contextᵗ Δ &
    substitutionᵗ Γᵗ Δᵗ σ
  } }

with trans_istype {Γ A} (H : Stt.istype Γ A) {struct H} :
  { Γᵗ : contextᵗ Γ &
    typeᵗ Γᵗ A
  }

with trans_isterm {Γ A u} (H : Stt.isterm Γ u A) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Aᵗ : typeᵗ Γᵗ A &
    termᵗ Aᵗ u
  } }

with trans_eqctx {Γ Δ} (H : Stt.eqctx Γ Δ) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Δᵗ : contextᵗ Δ &
    eqctxᵗ Γᵗ Δᵗ
  } }

with trans_eqsubst {Γ Δ σ ρ} (H : Stt.eqsubst σ ρ Γ Δ) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Δᵗ : contextᵗ Δ &
  { σᵗ : substitutionᵗ Γᵗ Δᵗ σ &
  { ρᵗ : substitutionᵗ Γᵗ Δᵗ ρ &
    eqsubstᵗ σᵗ ρᵗ
  } } } }

with trans_eqtype {Γ A B} (H : Stt.eqtype Γ A B) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Aᵗ : typeᵗ Γᵗ A &
  { Bᵗ : typeᵗ Γᵗ B &
    eqtypeᵗ Aᵗ Bᵗ
  } } }

with trans_eqterm {Γ A u v} (H : Stt.eqterm Γ u v A) {struct H} :
  { Γᵗ : contextᵗ Γ &
  { Aᵗ : typeᵗ Γᵗ A &
  { uᵗ : termᵗ Aᵗ u &
  { vᵗ : termᵗ Aᵗ v &
    eqtermᵗ uᵗ vᵗ
  } } } }
.
Proof.
  (**** trans_isctx ****)
  - { dependent destruction H ; doConfig.

      (* CtxEmpty *)
      - { exact ctxemptyᵗ. }

      (* CtxExtend *)
      - { (* pose (Gᵗ := trans_isctx _ i). *)
          destruct (trans_istype _ _ i0) as [Gᵗ Aᵗ].
          exact (ctxextendᵗ Gᵗ Aᵗ).
        }
    }

  (**** trans_issubst ****)
  - { dependent destruction H ; doConfig.

      (* SubstZero *)
      - admit.

      (* SubstWeak *)
      - admit.

      (* SubstShift *)
      - admit.

      (* SubstId *)
      - admit.

      (* SubstComp *)
      - admit.

      (* SubstCtxConv *)
      - admit.
    }

  (**** trans_istype ****)
  - { dependent destruction H ; doConfig.

      (* TyCtxConv *)
      - admit.

      (* TySubst *)
      - admit.

      (* TyProd *)
      - { destruct (trans_istype _ _ H) as [GAᵗ Bᵗ].
          (* We seem to need inversion to recover some Gᵗ and Aᵗ
             or, we could maybe translate the other hypotheses to get them
             and then use some lemma to identify them in some way. *)
          admit.
        }

      (* TyId *)
      - { destruct (trans_istype _ _ i0) as [Gᵗ Aᵗ].
          destruct (trans_isterm _ _ _ i1) as [Gᵗ' [Aᵗ' uᵗ]].
          destruct (trans_isterm _ _ _ i2) as [Gᵗ'' [Aᵗ'' vᵗ]].
          (* Now we need to have a link between the different Gᵗs and Aᵗs.
             The best would be definitional equality (or even syntactic but
             I don't believe in it), but we might need some transport already.
           *)
          admit.
        }

      (* TyBool *)
      - admit.
    }

  (**** trans_isterm ****)
  - { dependent destruction H ; doConfig.

      (* TermTyConv *)
      - admit.

      (* TermCtxConv *)
      - admit.

      (* TermSubst *)
      - admit.

      (* TermVarZero *)
      - admit.

      (* TermVarSucc *)
      - admit.

      (* TermAbs *)
      - admit.

      (* TermApp *)
      - admit.

      (* TermRefl *)
      - { destruct (trans_isterm _ _ _ H) as [Gᵗ [Aᵗ uᵗ]].
          exists Gᵗ. admit.
        }

      (* TermTrue *)
      - admit.

      (* TermFalse *)
      - admit.

      (* TermCond *)
      - admit.
    }

  (**** trans_eqctx ****)
  - { dependent destruction H ; doConfig.

      (* CtxRefl *)
      - admit.

      (* CtxSym *)
      - admit.

      (* CtxTrans *)
      - admit.

      (* EqCtxEmpty *)
      - admit.

      (* EqCtxExtend *)
      - admit.
    }

  (**** trans_eqsubst ****)
  - { dependent destruction H ; doConfig.

      (* SubstRefl *)
      - admit.

      (* SubstSym *)
      - admit.

      (* SubstTrans *)
      - admit.

      (* CongSubstZero *)
      - admit.

      (* CongSubstWeak *)
      - admit.

      (* CongSubstShift *)
      - admit.

      (* CongSubstComp *)
      - admit.

      (* EqSubstCtxConv *)
      - admit.

      (* CompAssoc *)
      - admit.

      (* WeakNat *)
      - admit.

      (* WeakZero *)
      - admit.

      (* ShiftZero *)
      - admit.

      (* CompShift *)
      - admit.

      (* CompIdRight *)
      - admit.

      (* CompIdLeft *)
      - admit.
    }

  (**** trans_eqtype ****)
  - { dependent destruction H ; doConfig.

      (* EqTyCtxConv *)
      - admit.

      (* EqTyRefl *)
      - admit.

      (* EqTySym *)
      - admit.

      (* EqTyTrans *)
      - admit.

      (* EqTyIdSubst *)
      - admit.

      (* EqTySubstComp *)
      - admit.

      (* EqTySubstProd *)
      - admit.

      (* EqTySubstId *)
      - admit.

      (* EqTySubstBool *)
      - admit.

      (* CongProd *)
      - admit.

      (* CongId *)
      - admit.

      (* CongTySubst *)
      - admit.
    }

  (**** trans_eqterm ****)
  - { dependent destruction H ; doConfig.

      (* EqTyConv *)
      - admit.

      (* EqCtxConv *)
      - admit.

      (* EqRefl *)
      - admit.

      (* EqSym *)
      - admit.

      (* EqTrans *)
      - admit.

      (* EqIdSubst *)
      - admit.

      (* EqSubstComp *)
      - admit.

      (* EqSubstWeak *)
      - admit.

      (* EqSubstZeroZero *)
      - admit.

      (* EqSubstZeroSucc *)
      - admit.

      (* EqSubstShiftZero *)
      - admit.

      (* EqSubstShiftSucc *)
      - admit.

      (* EqSubstAbs *)
      - admit.

      (* EqSubstApp *)
      - admit.

      (* EqSubstRefl *)
      - admit.

      (* EqSubstTrue *)
      - admit.

      (* EqSubstFalse *)
      - admit.

      (* EqSubstCond *)
      - admit.

      (* BoolReflection *)
      - { destruct (trans_isterm _ _ _ i2) as [Gᵗ [Eqᵗ pᵗ]].
          exists Gᵗ.
          simple refine (existT _ _ _).
          - unshelve (eapply mktypeᵗ).
            + exact 0.
            + eapply teletype_one. exact Bool.
            + simpl. capply TyBool.
              admit.
          - (* Now we'd like some inversion on Eqᵗ to get some Aᵗ, uᵗ and vᵗ. *)
            (* I was hoping this case would help me see how to build the ᵗ
               types... *)
            (* In a way, the Aᵗ, uᵗ and vᵗ we would get would be what would
               fill the only hole for each. *)
          admit.
        }

      (* ProdBeta *)
      - admit.

      (* CondTrue *)
      - admit.

      (* CondFalse *)
      - admit.

      (* CongAbs *)
      - admit.

      (* CongApp *)
      - admit.

      (* CongRefl *)
      - admit.

      (* CongCond *)
      - admit.

      (* CongTermSubst *)
      - admit.
    }
Qed.

End Translation.

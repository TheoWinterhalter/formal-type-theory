(* Forgetting Annotation

   We propose a straightforward translation from annotated syntax to concise
   syntax. We also prove the obvious statement that typing is preserved.
 *)

Require config.
Require Import config_tactics.

Require syntax.
Require Import tt.
Require annotated_syntax concise_syntax.

(* Annotated theory *)
Module Att.

  Section Att.

    Context `{configPrecondition : config.Precondition}.
    Context `{configReflection : config.Reflection}.
    Context `{configBinaryProdType : config.BinaryProdType}.
    Context `{configProdEta : config.ProdEta}.
    Context `{configUniverses : config.Universes}.
    Context `{configPropType : config.PropType}.
    Context `{configIdType : config.IdType}.
    Context `{configIdEliminator : config.IdEliminator}.
    Context `{configEmptyType : config.EmptyType}.
    Context `{configUnitType : config.UnitType}.
    Context `{configBoolType : config.BoolType}.
    Context `{configProdType : config.ProdType}.

    Local Existing Instance annotated_syntax.Syntax.

    Definition context := annotated_syntax.context.
    Definition type := annotated_syntax.type.
    Definition term := annotated_syntax.term.
    Definition substitution := annotated_syntax.substitution.

    Definition isctx   := isctx.
    Definition issubst := issubst.
    Definition istype  := istype.
    Definition isterm  := isterm.
    Definition eqctx   := eqctx.
    Definition eqsubst := eqsubst.
    Definition eqtype  := eqtype.
    Definition eqterm  := eqterm.

  End Att.

End Att.

Module A := annotated_syntax.

(* Concise theory *)
Module Ctt.

  Section Ctt.

    Context `{configPrecondition : config.Precondition}.
    Context `{configReflection : config.Reflection}.
    Context `{configBinaryProdType : config.BinaryProdType}.
    Context `{configProdEta : config.ProdEta}.
    Context `{configUniverses : config.Universes}.
    Context `{configPropType : config.PropType}.
    Context `{configIdType : config.IdType}.
    Context `{configIdEliminator : config.IdEliminator}.
    Context `{configEmptyType : config.EmptyType}.
    Context `{configUnitType : config.UnitType}.
    Context `{configBoolType : config.BoolType}.
    Context `{configProdType : config.ProdType}.

    Local Existing Instance concise_syntax.Syntax.

    Definition context := concise_syntax.context.
    Definition term := concise_syntax.term.
    Definition substitution := concise_syntax.substitution.

    Definition isctx   := isctx.
    Definition issubst := issubst.
    Definition istype  := istype.
    Definition isterm  := isterm.
    Definition eqctx   := eqctx.
    Definition eqsubst := eqsubst.
    Definition eqtype  := eqtype.
    Definition eqterm  := eqterm.

  End Ctt.

End Ctt.

Module C := concise_syntax.

Section Translation.

Context `{configPrecondition : config.Precondition}.
Context `{configReflection : config.Reflection}.
Context `{configBinaryProdType : config.BinaryProdType}.
Context `{configProdEta : config.ProdEta}.
Context `{configUniverses : config.Universes}.
Context `{configPropType : config.PropType}.
Context `{configIdType : config.IdType}.
Context `{configIdEliminator : config.IdEliminator}.
Context `{configEmptyType : config.EmptyType}.
Context `{configUnitType : config.UnitType}.
Context `{configBoolType : config.BoolType}.
Context `{configProdType : config.ProdType}.

Fixpoint forget_type (A : Att.type) : Ctt.term :=
  match A with
  | A.Prod A B => C.Prod (forget_type A) (forget_type B)
  | A.Id A u v => C.Id (forget_type A) (forget_term u) (forget_term v)
  | A.Subst A sbs => C.subst (forget_type A) (forget_subst sbs)
  | A.Empty => C.Empty
  | A.Unit => C.Unit
  | A.Bool => C.Bool
  | A.BinaryProd A B => C.BinaryProd (forget_type A) (forget_type B)
  | A.Uni l => C.Uni l
  | A.El l u => forget_term u
  end

with forget_term (u : Att.term) : Ctt.term :=
  match u with
  | A.var x => C.var x
  | A.lam A B t => C.lam (forget_type A) (forget_term t)
  | A.app u A B v => C.app (forget_term u) (forget_term v)
  | A.refl A u => C.refl (forget_term u)
  | A.j A u C w v p =>
    C.j (forget_type A)
        (forget_term u)
        (forget_type C)
        (forget_term w)
        (forget_term v)
        (forget_term p)
  | A.subst u sbs => C.subst (forget_term u) (forget_subst sbs)
  | A.exfalso A u => C.exfalso (forget_type A) (forget_term u)
  | A.unit => C.unit
  | A.true => C.true
  | A.false => C.false
  | A.cond C u v w =>
    C.cond (forget_type C) (forget_term u) (forget_term v) (forget_term w)
  | A.pair A B u v =>
    C.pair (forget_type A) (forget_type B) (forget_term u) (forget_term v)
  | A.proj1 A B p =>
    C.proj1 (forget_type A) (forget_type B) (forget_term p)
  | A.proj2 A B p =>
    C.proj2 (forget_type A) (forget_type B) (forget_term p)
  | A.uniProd l1 l2 a b =>
    C.Prod (forget_term a) (forget_term b)
  | A.uniId l a u v =>
    C.Id (forget_term a) (forget_term u) (forget_term v)
  | A.uniEmpty l => C.Empty
  | A.uniUnit l => C.Unit
  | A.uniBool n => C.Bool
  | A.uniBinaryProd l1 l2 a b =>
    C.BinaryProd (forget_term a) (forget_term b)
  | A.uniUni l => C.Uni l
  end

with forget_subst (sbs : Att.substitution) : Ctt.substitution :=
  match sbs with
  | A.sbzero A u => C.sbzero (forget_type A) (forget_term u)
  | A.sbweak A => C.sbweak (forget_type A)
  | A.sbshift A sbs => C.sbshift (forget_type A) (forget_subst sbs)
  | A.sbid => C.sbid
  | A.sbcomp sbs sbt => C.sbcomp (forget_subst sbs) (forget_subst sbt)
  end.

Axiom admit : forall {A}, A.
Tactic Notation "admit" := (exact admit).

Fixpoint forget_ctx (G : Att.context) : Ctt.context :=
  match G with
  | A.ctxempty => C.ctxempty
  | A.ctxextend G A => C.ctxextend (forget_ctx G) (forget_type A)
  end.


Ltac ih :=
  match goal with
  | forget_isctx :
      forall G,
        Att.isctx G ->
        Ctt.isctx (forget_ctx G)
    |- tt.isctx (forget_ctx ?G) =>
    now apply (forget_isctx G)
  | forget_istype :
      forall G A,
        Att.istype G A ->
        Ctt.istype (forget_ctx G) (forget_type A)
    |- tt.istype (forget_ctx ?G) (forget_type ?A) =>
    now apply (forget_istype G A)
  | forget_isterm :
      forall G u A,
        Att.isterm G u A ->
        Ctt.isterm (forget_ctx G) (forget_term u) (forget_type A)
    |- tt.isterm (forget_ctx ?G) (forget_term ?u) (forget_type ?A) =>
    now apply (forget_isterm G u A)
  | forget_issubst :
      forall sbs G D,
        Att.issubst sbs G D ->
        Ctt.issubst (forget_subst sbs) (forget_ctx G) (forget_ctx D)
    |- tt.issubst (forget_subst ?sbs) (forget_ctx ?G) (forget_ctx ?D) =>
    now apply (forget_issubst sbs G D)
  | forget_eqctx :
      forall G D,
        Att.eqctx G D ->
        Ctt.eqctx (forget_ctx G) (forget_ctx D)
    |- tt.eqctx (forget_ctx ?G) (forget_ctx ?D) =>
    now apply (forget_eqctx G D)
  | forget_eqtype :
      forall G A B,
        Att.eqtype G A B ->
        Ctt.eqtype (forget_ctx G) (forget_type A) (forget_type B)
    |- tt.eqtype (forget_ctx ?G) (forget_type ?A) (forget_type ?B) =>
    now apply (forget_eqtype G A B)
  | forget_eqterm :
      forall G u v A,
        Att.eqterm G u v A ->
        Ctt.eqterm (forget_ctx G) (forget_term u) (forget_term v) (forget_type A)
    |- tt.eqterm (forget_ctx ?G) (forget_term ?u) (forget_term ?v) (forget_type ?A) =>
    now apply (forget_eqterm G u v A)
  | forget_eqsubst :
      forall sbs sbt G D,
        Att.eqsubst sbs sbt G D ->
        Ctt.eqsubst (forget_subst sbs)
                    (forget_subst sbt)
                    (forget_ctx G)
                    (forget_ctx D)
    |- tt.eqsubst (forget_subst ?sbs)
              (forget_subst ?sbt)
              (forget_ctx ?G)
              (forget_ctx ?D) =>
    now apply (forget_eqsubst sbs sbt G D)
  end.


Fixpoint forget_isctx {G} (H : Att.isctx G) {struct H} :
  Ctt.isctx (forget_ctx G)

with forget_istype {G A} (H : Att.istype G A) {struct H} :
  Ctt.istype (forget_ctx G) (forget_type A)

with forget_isterm {G u A} (H : Att.isterm G u A) {struct H} :
  Ctt.isterm (forget_ctx G) (forget_term u) (forget_type A)

with forget_issubst {sbs G D} (H : Att.issubst sbs G D) {struct H} :
  Ctt.issubst (forget_subst sbs) (forget_ctx G) (forget_ctx D)

with forget_eqctx {G D} (H : Att.eqctx G D) {struct H} :
  Ctt.eqctx (forget_ctx G) (forget_ctx D)

with forget_eqtype {G A B} (H : Att.eqtype G A B) {struct H} :
  Ctt.eqtype (forget_ctx G) (forget_type A) (forget_type B)

with forget_eqterm {G u v A} (H : Att.eqterm G u v A) {struct H} :
  Ctt.eqterm (forget_ctx G) (forget_term u) (forget_term v) (forget_type A)

with forget_eqsubst {sbs sbt G D} (H : Att.eqsubst sbs sbt G D) {struct H} :
  Ctt.eqsubst
    (forget_subst sbs)
    (forget_subst sbt)
    (forget_ctx G)
    (forget_ctx D).

Proof.
  (* forget_isctx *)
  - { destruct H ; doConfig.

      (* CtxEmpty *)
      - constructor.

      (* CtxExtend *)
      - simpl. (config constructor) ; ih.
    }

  (* forget_istype *)
  - { destruct H ; doConfig.

      (* TyCtxConv *)
      - { (config apply @TyCtxConv with (G := forget_ctx G)) ; ih. }

      (* TySubst *)
      - { simpl.
          config apply @TySubst with (D := forget_ctx D).
          - ih.
          - ih.
          - ih.
          - ih.
        }

      (* TyProd *)
      - { simpl. capply @TyProd.
          - apply (forget_istype _ _ H).
          - ih.
          - ih.
        }

      (* TyId *)
      - { simpl. capply @TyId.
          - ih.
          - ih.
          - ih.
          - ih.
        }

      (* TyEmpty *)
      - capply @TyEmpty ; ih.

      (* TyUnit *)
      - capply @TyUnit ; ih.

      (* TyBool *)
      - capply @TyBool ; ih.

      (* TyBinaryProd *)
      - { simpl. capply @TyBinaryProd.
          - ih.
          - ih.
          - ih.
        }

      (* TyUni *)
      - { simpl. capply @TyUni. ih. }

      (* TyEl *)
      - { simpl.
          pose (tyel := @tt.TyEl configPrecondition configReflection configBinaryProdType configProdEta configUniverses configPropType configIdEliminator configEmptyType configUnitType configBoolType configIdType configProdType concise_syntax.Syntax). cbv in tyel.
          config (eapply tyel).
          - auto.
          - apply (forget_isterm _ _ _ i).
          - intro x.
            specialize (i0 x). ih.
        }

    }

  (* forget_isterm *)
  - { destruct H ; doConfig.

      (* TermTyConv *)
      - { (config apply @TermTyConv with (A := forget_type A)) ; ih. }

      (* TermCtxConv *)
      - { (config apply @TermCtxConv with (G := forget_ctx G)) ; ih. }

      (* TermSubst *)
      - { simpl. (config apply @TermSubst with (D := forget_ctx D)) ; ih. }

      (* TermVarZero *)
      - { simpl. (capply @TermVarZero) ; ih. }

      (* TermVarSucc *)
      - { simpl. capply @TermVarSucc.
          - ih.
          - ih.
          - now apply (forget_isterm G (A.var k) A).
          - ih.
        }

      (* TermAbs *)
      - { simpl.
          (* Here is an example of where things are annoying as well.
             Coq can't unify C.lam and syntax.lam as they don't have the same
             amount of arguments even though they are actually the same in this
             particular case.
           *)
          pose (TA := @TermAbs).
          specialize TA
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_type A) (forget_term u) (forget_type B).
          simpl in TA. capply TA.
          - ih.
          - ih.
          - apply (forget_istype _ _ i1).
          - apply (forget_isterm _ _ _ H).
        }

      (* TermApp *)
      - { simpl.
          pose (TA := @TermApp).
          specialize TA
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_type A) (forget_type B)
               (forget_term u) (forget_term v).
          simpl in TA.
          capply TA.
          - ih.
          - ih.
          - apply (forget_istype _ _ i1).
          - apply (forget_isterm _ _ _ H).
          - ih.
        }

      (* TermRefl *)
      - { simpl.
          pose (TR := @TermRefl).
          specialize TR
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_type A) (forget_term u).
          simpl in TR.
          capply TR ; ih.
        }

      (* TermJ *)
      - { simpl. capply @TermJ.
          - ih.
          - ih.
          - ih.
          - now apply (forget_istype _ _ i1).
          - now apply (forget_isterm _ _ _ H0).
          - ih.
          - now apply (forget_isterm _ _ _ H2).
        }

      (* TermExfalso *)
      - { simpl. capply @TermExfalso.
          - ih.
          - ih.
          - now apply (forget_isterm _ _ _ H).
        }

      (* TermUnit *)
      - { simpl. capply @TermUnit. ih. }

      (* TermTrue *)
      - { simpl. capply @TermTrue. ih. }

      (* TermFalse *)
      - { simpl. capply @TermFalse. ih. }

      (* TermCond *)
      - { simpl. capply @TermCond.
          - ih.
          - now apply (forget_isterm _ _ _ H).
          - now apply (forget_istype _ _ i0).
          - now apply (forget_isterm _ _ _ H0).
          - now apply (forget_isterm _ _ _ H1).
        }

      (* TermPair *)
      - { simpl. capply @TermPair ; ih. }

      (* TermProjOne *)
      - { simpl. capply @TermProjOne.
          - ih.
          - ih.
          - ih.
          - now apply (forget_isterm _ _ _ H).
        }

      (* TermProjTwo *)
      - { simpl. capply @TermProjTwo.
          - ih.
          - ih.
          - ih.
          - now apply (forget_isterm _ _ _ H).
        }

      (* TermUniProd *)
      - { simpl.
          pose (TU := @TermUniProd).
          specialize TU
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term b) n m.
          simpl in TU.
          capply TU.
          - now apply (forget_isterm _ _ _ H).
          - now apply (forget_isterm _ _ _ H0).
          - ih.
        }

      (* TermUniProdProp *)
      - { simpl.
          pose (TU := @TermUniProdProp).
          specialize TU
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term b) l.
          simpl in TU.
          ceapply TU.
          - now apply (forget_isterm _ _ _ H).
          - now apply (forget_isterm _ _ _ H0).
          - ih.
        }

      (* TermUniId *)
      - { simpl.
          pose (TU := @TermUniId).
          specialize TU
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term u) (forget_term v) n.
          simpl in TU.
          capply TU.
          - now apply (forget_isterm _ _ _ H).
          - now apply (forget_isterm _ _ _ H0).
          - now apply (forget_isterm _ _ _ H1).
          - ih.
        }

      (* TermUniEmpty *)
      - { simpl.
          pose (TU := @TermUniEmpty).
          specialize TU
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) n.
          simpl in TU.
          capply TU. ih.
        }

      (* TermUniUnit *)
      - { simpl.
          pose (TU := @TermUniUnit).
          specialize TU
          with configPrecondition configReflection configBinaryProdType
                                  configProdEta configUniverses configPropType configIdEliminator
                                  configEmptyType configUnitType configBoolType configIdType
                                  configProdType concise_syntax.Syntax
                                  (forget_ctx G) n.
          simpl in TU.
          capply TU. ih.
        }

      (* TermUniBool *)
      - { simpl.
          pose (TU := @TermUniBool).
          specialize TU
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) n.
          simpl in TU.
          capply TU. ih.
        }

      (* TermUniBinaryProd *)
      - { simpl.
          pose (TU := @TermUniBinaryProd).
          specialize TU
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term b) n m.
          simpl in TU.
          capply TU.
          - now apply (forget_isterm _ _ _ H).
          - now apply (forget_isterm _ _ _ H0).
          - ih.
        }

      (* TermUniBinaryProdProp *)
      - { simpl.
          pose (TU := @TermUniBinaryProdProp).
          specialize TU
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term b).
          simpl in TU.
          capply TU.
          - now apply (forget_isterm _ _ _ H).
          - now apply (forget_isterm _ _ _ H0).
          - ih.
        }

      (* TermUniUni *)
      - { simpl. capply @TermUniUni. ih. }

      (* TermUniProp *)
      - { simpl. capply @TermUniProp. ih. }
    }

  (* forget_issubst *)
  - { destruct H ; doConfig.

      (* SubstZerp *)
      - { simpl. capply @SubstZero ; ih. }

      (* SubstWeak *)
      - { simpl. capply @SubstWeak ; ih. }

      (* SubstShift *)
      - { simpl. capply @SubstShift ; ih. }

      (* SubstId *)
      - { simpl. capply @SubstId ; ih. }

      (* SubstComp *)
      - { simpl. (config apply @SubstComp with (D := forget_ctx D)) ; ih. }


      (* SubstCtxConv *)
      - { (config apply @SubstCtxConv with (G1 := forget_ctx G1) (D1 := forget_ctx D1)) ; ih. }
    }

  (* forget_eqctx *)
  - { destruct H ; doConfig.

      (* CtxRefl *)
      - { capply CtxRefl. ih. }

      (* CtxSym *)
      - { capply CtxSym ; ih. }

      (* CtxTrans *)
      - { (config apply @CtxTrans with (D := forget_ctx D)) ; ih. }


      (* EqCtxEmpty *)
      - { capply @EqCtxEmpty. }

      (* EqCtxExtend *)
      - { simpl. capply @EqCtxExtend ; ih. }

    }

  (* forget_eqtype *)
  - { destruct H ; doConfig.

      (* EqTyCtxConv *)
      - { (config apply @EqTyCtxConv with (G := forget_ctx G)) ; ih. }

      (* EqTyRefl *)
      - { capply EqTyRefl ; ih. }

      (* EqTySym *)
      - { capply EqTySym ; ih. }

      (* EqTyTrans *)
      - { (config apply @EqTyTrans with (B := forget_type B)) ; ih. }

      (* EqTyIdSubst *)
      - { simpl. capply @EqTyIdSubst ; ih. }

      (* EqTySubstComp *)
      - { simpl.
          (config apply @EqTySubstComp with (D := forget_ctx D) (E := forget_ctx E)) ; ih.
        }

      (* EqTySubstProd *)
      - { simpl. config eapply @EqTySubstProd with (D := forget_ctx D).
          - ih.
          - ih.
          - now apply (forget_istype _ _ i1).
          - ih.
          - ih.
        }

      (* EqTySubstId *)
      - { simpl. (config apply @EqTySubstId with (D := forget_ctx D)) ; ih. }

      (* EqTySubstEmpty *)
      - { simpl. (config apply @EqTySubstEmpty with (D := forget_ctx D)) ; ih. }

      (* EqTySubstUnit *)
      - { simpl. (config apply @EqTySubstUnit with (D := forget_ctx D)) ; ih. }

      (* EqTySubstBool *)
      - { simpl. (config apply @EqTySubstBool with (D := forget_ctx D)) ; ih. }

      (* EqTyExfalso *)
      - { config apply @EqTyExfalso with (u := forget_term u).
          - ih.
          - ih.
          - ih.
          - now apply (forget_isterm _ _ _ i2).
        }

      (* CongProd *)
      - { simpl. capply @CongProd ; try ih.
          - now apply (forget_istype _ _ i1).
          - now apply (forget_istype _ _ i3).
          - now apply (forget_eqtype _ _ _ H0).
        }

      (* CongId *)
      - { simpl. capply @CongId ; ih. }

      (* CongTySubst *)
      - { simpl. (config apply @CongTySubst with (D := forget_ctx D)) ; ih. }

      (* CongBinaryProd *)
      - { simpl. capply @CongBinaryProd ; ih. }

      (* EqTySubstBinaryProd *)
      - { simpl.
          (config apply @EqTySubstBinaryProd with (D := forget_ctx D)) ; ih.
        }

      (* EqTySubstUni *)
      - { simpl. (config apply @EqTySubstUni with (D := forget_ctx D)) ; ih. }

      (* ElProd *)
      - { simpl.
          pose (P := @ElProd).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term b) n m.
          simpl in P.
          (config apply @P with (n := n) (m := m)).
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - ih.
        }

      (* ElProdProp *)
      - { simpl.
          pose (P := @ElProdProp).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term b) l.
          simpl in P.
          ceapply P.
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - ih.
        }

      (* ElId *)
      - { simpl.
          pose (P := @ElId).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term u) (forget_term v) n.
          simpl in P.
          ceapply P.
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
          - ih.
        }

      (* ElSubst *)
      - { simpl.
          pose (P := @ElSubst).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_ctx D) (forget_term a)
               n (forget_subst sbs).
          simpl in P.
          ceapply P.
          - now apply (forget_issubst _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - ih.
          - ih.
        }

      (* ElEmpty *)
      - { simpl.
          pose (P := @ElEmpty).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) n.
          simpl in P.
          ceapply P.
          - assumption.
          - ih.
        }

      (* ElUnit *)
      - { simpl.
          pose (P := @ElUnit).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) n.
          simpl in P.
          ceapply P.
          - assumption.
          - ih.
        }

      (* ElBool *)
      - { simpl.
          pose (P := @ElBool).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) n.
          simpl in P.
          ceapply P.
          - assumption.
          - ih.
        }

      (* ElBinaryProd *)
      - { simpl.
          pose (P := @ElBinaryProd).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term b) n m.
          simpl in P.
          ceapply P.
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - ih.
        }

      (* ElBinaryProdProp *)
      - { simpl.
          pose (P := @ElBinaryProdProp).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term b).
          simpl in P.
          ceapply P.
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - ih.
        }

      (* ElUni *)
      - { simpl.
          pose (P := @ElUni).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) n.
          simpl in P.
          capply P. ih.
        }

      (* ElProp *)
      - { simpl.
          pose (P := @ElProp).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G).
          simpl in P.
          capply P. ih.
        }

      (* CongEl *)
      - { simpl.
          pose (P := @CongEl).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_term a) (forget_term b) n.
          simpl in P.
          ceapply P.
          - now apply (forget_eqterm _ _ _ _ e).
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - ih.
        }
    }

  (* forget_eqterm *)
  - { destruct H ; doConfig.

      (* EqTyConv *)
      - { (config apply @EqTyConv with (A := forget_type A)) ; ih. }

      (* EqCtxConv *)
      - { (config apply @EqCtxConv with (G := forget_ctx G)) ; ih. }

      (* EqRefl *)
      - { capply EqRefl ; ih. }

      (* EqSym *)
      - { capply EqSym ; ih. }

      (* EqTrans *)
      - { (config apply @EqTrans with (v := forget_term v)) ; ih. }

      (* EqIdSubst *)
      - { simpl. capply @EqIdSubst ; ih. }

      (* EqSubstComp *)
      - { simpl.
          (config apply @EqSubstComp with (D := forget_ctx D) (E := forget_ctx E)) ; ih.
        }

      (* EqSubstWeak *)
      - { simpl. capply @EqSubstWeak ; try ih.
          now apply (forget_isterm _ _ _ i1).
        }

      (* EqSubstZeroZero *)
      - { simpl. capply @EqSubstZeroZero ; ih. }

      (* EqSubstZeroSucc *)
      - { simpl. capply @EqSubstZeroSucc ; try ih.
          now apply (forget_isterm _ _ _ i2).
        }

      (* EqSubstShiftZero *)
      - { simpl.
          (config apply @EqSubstShiftZero with (D := forget_ctx D)) ; ih.
        }

      (* EqSubstShiftSucc *)
      - { simpl.
          (config apply @EqSubstShiftSucc with (D := forget_ctx D)) ; try ih.
          now apply (forget_isterm _ _ _ i3).
        }

      (* EqSubstAbs *)
      - { simpl.
          pose (P := @EqSubstAbs).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_ctx D) (forget_type A) (forget_type B)
               (forget_term u) (forget_subst sbs).
          simpl in P.
          ceapply P.
          - ih.
          - now apply (forget_isctx _ i0).
          - ih.
          - now apply (forget_istype _ _ i2).
          - now apply (forget_isterm _ _ _ i3).
          - ih.
        }

      (* EqSubstApp *)
      - { simpl.
          pose (P := @EqSubstApp).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_ctx D) (forget_type A) (forget_type B)
               (forget_term u) (forget_term v) (forget_subst sbs).
          simpl in P.
          ceapply P.
          - ih.
          - now apply (forget_isctx _ i0).
          - ih.
          - now apply (forget_istype _ _ i2).
          - now apply (forget_isterm _ _ _ i3).
          - ih.
          - ih.
        }

      (* EqSubstRefl *)
      - { simpl.
          pose (P := @EqSubstRefl).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_ctx D) (forget_type A)
               (forget_term u) (forget_subst sbs).
          simpl in P.
          ceapply P.
          - now apply (forget_issubst _ _ _ i).
          - ih.
          - ih.
          - ih.
          - ih.
        }

      (* EqSubstJ *)
      - { simpl. (config apply @EqSubstJ with (D := forget_ctx D)) ; try ih.
          - now apply (forget_istype _ _ i4).
          - now apply (forget_isterm _ _ _ i5).
          - now apply (forget_isterm _ _ _ i7).
        }

      (* EqSubstExfalso *)
      - { simpl.
          (config apply @EqSubstExfalso with (D := forget_ctx D)) ; try ih.
          now apply (forget_isterm _ _ _ i2).
        }

      (* EqSubstUnit *)
      - { simpl. (config apply @EqSubstUnit with (D := forget_ctx D)) ; ih. }

      (* EqSubstTrue *)
      - { simpl. (config apply @EqSubstTrue with (D := forget_ctx D)) ; ih. }

      (* EqSubstFalse *)
      - { simpl. (config apply @EqSubstFalse with (D := forget_ctx D)) ; ih. }

      (* EqSubstCond *)
      - { simpl. (config apply @EqSubstCond with (D := forget_ctx D)) ; try ih.
          - now apply (forget_isterm _ _ _ i2).
          - now apply (forget_istype _ _ i3).
          - now apply (forget_isterm _ _ _ i4).
          - now apply (forget_isterm _ _ _ i5).
        }

      (* EqTermExfalso *)
      - { (config apply @EqTermExfalso with (w := forget_term w)) ; try ih.
          now apply (forget_isterm _ _ _ i3).
        }

      (* UnitEta *)
      - { simpl. capply @UnitEta.
          - ih.
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
        }

      (* EqReflection *)
      - { (config apply @EqReflection with (p := forget_term p)) ; try ih.
          now apply (forget_isterm _ _ _ i3).
        }

      (* ProdBeta *)
      - { simpl.
          pose (P := @ProdBeta).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_type A) (forget_type B)
               (forget_term u) (forget_term v).
          simpl in P.
          ceapply P ; try ih.
          - now apply (forget_istype _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
        }

      (* CondTrue *)
      - { simpl. capply @CondTrue.
          - ih.
          - now apply (forget_istype _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
        }

      (* CondFalse *)
      - { simpl. capply @CondFalse.
          - ih.
          - now apply (forget_istype _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
        }

      (* ProdEta *)
      - { simpl. capply @ProdEta ; try ih.
          - now apply (forget_istype _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
          - now apply (forget_isterm _ _ _ i3).
          - now apply (forget_eqterm _ _ _ _ H).
        }

      (* JRefl *)
      - { simpl. capply @JRefl ; try ih.
          - now apply (forget_istype _ _ i2).
          - now apply (forget_isterm _ _ _ i3).
        }

      (* CongAbs *)
      - { simpl.
          pose (P := @CongAbs).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_type A1) (forget_type A2) (forget_type B1)
               (forget_type B2) (forget_term u1) (forget_term u2).
          simpl in P.
          ceapply P ; try ih.
          - now apply (forget_istype _ _ i2).
          - now apply (forget_istype _ _ i3).
          - now apply (forget_isterm _ _ _ i4).
          - now apply (forget_isterm _ _ _ i5).
          - now apply (forget_eqtype _ _ _ e0).
          - now apply (forget_eqterm _ _ _ _ H).
        }

      (* CongApp *)
      - { simpl.
          pose (P := @CongApp).
          specialize P
          with configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               (forget_ctx G) (forget_type A1) (forget_type A2) (forget_type B1)
               (forget_type B2) (forget_term u1) (forget_term u2)
               (forget_term v1) (forget_term v2).
          simpl in P.
          ceapply P ; try ih.
          - now apply (forget_istype _ _ i1).
          - now apply (forget_istype _ _ i2).
          - now apply (forget_istype _ _ i3).
          - now apply (forget_isterm _ _ _ i4).
          - now apply (forget_isterm _ _ _ i5).
          - ih.
          - now apply (forget_eqtype _ _ _ e0).
          - now apply (forget_eqterm _ _ _ _ H).
        }

      (* CongRefl *)
      - { simpl.
          capply (@CongRefl
               configPrecondition configReflection configBinaryProdType
               configProdEta configUniverses configPropType configIdEliminator
               configEmptyType configUnitType configBoolType configIdType
               configProdType concise_syntax.Syntax
               f (forget_ctx G) (forget_term u1) (forget_term u2)
               (forget_type A1) (forget_type A2)) ; ih.
        }

      (* CongJ *)
      - { simpl. capply @CongJ ; try ih.
          - now apply (forget_istype _ _ i2).
          - now apply (forget_istype _ _ i3).
          - now apply (forget_isterm _ _ _ i8).
          - now apply (forget_isterm _ _ _ i9).
          - now apply (forget_eqtype _ _ _ e0).
          - now apply (forget_isterm _ _ _ i10).
          - now apply (forget_isterm _ _ _ i11).
          - now apply (forget_eqterm _ _ _ _ H0).
          - now apply (forget_eqterm _ _ _ _ H2).
        }

      (* CongCond *)
      - { simpl. capply @CongCond.
          - ih.
          - now apply (forget_istype _ _ i0).
          - now apply (forget_istype _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
          - now apply (forget_isterm _ _ _ i3).
          - now apply (forget_isterm _ _ _ i4).
          - now apply (forget_isterm _ _ _ i5).
          - now apply (forget_isterm _ _ _ i6).
          - now apply (forget_isterm _ _ _ i7).
          - now apply (forget_eqterm _ _ _ _ H).
          - now apply (forget_eqtype _ _ _ e).
          - now apply (forget_eqterm _ _ _ _ H0).
          - now apply (forget_eqterm _ _ _ _ H1).
        }

      (* CongTermSubst *)
      - { simpl. (config apply @CongTermSubst with (D := forget_ctx D)) ; ih. }

      (* CongPair *)
      - { simpl. capply @CongPair ; ih. }

      (* CongProjOne *)
      - { simpl. capply @CongProjOne ; try ih.
          - now apply (forget_eqterm _ _ _ _ H).
          - now apply (forget_isterm _ _ _ i4).
          - now apply (forget_isterm _ _ _ i5).
        }

      (* CongProjTwo *)
      - { simpl. capply @CongProjTwo ; try ih.
          - now apply (forget_eqterm _ _ _ _ H).
          - now apply (forget_isterm _ _ _ i4).
          - now apply (forget_isterm _ _ _ i5).
        }

      (* EqSubstPair *)
      - { simpl. (config apply @EqSubstPair with (D := forget_ctx D)) ; ih. }

      (* EqSubstProjOne *)
      - { simpl.
          (config apply @EqSubstProjOne with (D := forget_ctx D)) ; try ih.
          now apply (forget_isterm _ _ _ i0).
        }

      (* EqSubstProjTwo *)
      - { simpl.
          (config apply @EqSubstProjTwo with (D := forget_ctx D)) ; try ih.
          now apply (forget_isterm _ _ _ i0).
        }

      (* ProjOnePair *)
      - { simpl. capply @ProjOnePair ; ih. }

      (* ProjTwoPair *)
      - { simpl. capply @ProjTwoPair ; ih. }

      (* PairEta *)
      - { simpl. capply @PairEta ; try ih.
          - now apply (forget_eqterm _ _ _ _ H).
          - now apply (forget_eqterm _ _ _ _ H0).
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
        }

      (* EqSubstUniProd *)
      - { simpl.
          capply (@EqSubstUniProd
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0
            (forget_ctx G) (forget_ctx D) (forget_term a) (forget_term b)
            n m (forget_subst sbs)
          ) ; try ih.
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
        }

      (* EqSubstUniProdProp *)
      - { simpl.
          capply (@EqSubstUniProdProp
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0 f1
            (forget_ctx G) (forget_ctx D) (forget_term a) (forget_term b)
            l (forget_subst sbs)
          ) ; try ih.
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
        }

      (* EqSubstUniId *)
      - { simpl.
          capply (@EqSubstUniId
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0
            (forget_ctx G) (forget_ctx D) (forget_term a) (forget_term u)
            (forget_term v) n (forget_subst sbs)
          ) ; try ih.
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
        }

      (* EqSubstUniEmpty *)
      - { simpl.
          capply (@EqSubstUniEmpty
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0
            (forget_ctx G) (forget_ctx D) n (forget_subst sbs)
          ) ; ih.
        }

      (* EqSubstUniUnit *)
      - { simpl.
          capply (@EqSubstUniUnit
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0
            (forget_ctx G) (forget_ctx D) n (forget_subst sbs)
          ) ; ih.
        }

      (* EqSubstUniBool *)
      - { simpl.
          capply (@EqSubstUniBool
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0
            (forget_ctx G) (forget_ctx D) n (forget_subst sbs)
          ) ; ih.
        }

      (* EqSubstUniBinaryProd *)
      - { simpl.
          capply (@EqSubstUniBinaryProd
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0
            (forget_ctx G) (forget_ctx D) (forget_term a) (forget_term b)
            n m (forget_subst sbs)
          ) ; try ih.
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
        }

      (* EqSubstUniBinaryProdProp *)
      - { simpl.
          capply (@EqSubstUniBinaryProdProp
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0 f1
            (forget_ctx G) (forget_ctx D) (forget_term a) (forget_term b)
            (forget_subst sbs)
          ) ; try ih.
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
        }

      (* EqSubstUniUni *)
      - { simpl. (config apply @EqSubstUniUni with (D := forget_ctx D)) ; ih. }

      (* EqSubstUniProp *)
      - { simpl. (config apply @EqSubstUniProp with (D := forget_ctx D)) ; ih. }

      (* CongUniProd *)
      - { simpl.
          capply (@CongUniProd
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0
            (forget_ctx G) (forget_term a1) (forget_term a2) (forget_term b1)
            (forget_term b2) n m
          ) ; try ih.
          - now apply (forget_eqterm _ _ _ _ H).
          - now apply (forget_eqterm _ _ _ _ H0).
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
        }

      (* CongUniProdProp *)
      - { simpl.
          capply (@CongUniProdProp
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0 f1
            (forget_ctx G) (forget_term a1) (forget_term a2) (forget_term b1)
            (forget_term b2) l
          ) ; try ih.
          - now apply (forget_eqterm _ _ _ _ H).
          - now apply (forget_eqterm _ _ _ _ H0).
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
        }

      (* CongUniId *)
      - { simpl.
          capply (@CongUniId
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0
            (forget_ctx G) (forget_term a1) (forget_term a2)
            (forget_term u1) (forget_term u2)
            (forget_term v1) (forget_term v2) n
          ) ; try ih.
          - now apply (forget_eqterm _ _ _ _ H).
          - now apply (forget_eqterm _ _ _ _ H0).
          - now apply (forget_eqterm _ _ _ _ H1).
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
          - now apply (forget_isterm _ _ _ i3).
          - now apply (forget_isterm _ _ _ i4).
        }

      (* CongUniBinaryProd *)
      - { simpl.
          capply (@CongUniBinaryProd
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0
            (forget_ctx G) (forget_term a1) (forget_term a2)
            (forget_term b1) (forget_term b2) n m
          ) ; try ih.
          - now apply (forget_eqterm _ _ _ _ H).
          - now apply (forget_eqterm _ _ _ _ H0).
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
        }

      (* CongUniBinaryProdProp *)
      - { simpl.
          capply (@CongUniBinaryProdProp
            configPrecondition configReflection configBinaryProdType
            configProdEta configUniverses configPropType configIdEliminator
            configEmptyType configUnitType configBoolType configIdType
            configProdType concise_syntax.Syntax f f0 f1
            (forget_ctx G) (forget_term a1) (forget_term a2)
            (forget_term b1) (forget_term b2)
          ) ; try ih.
          - now apply (forget_eqterm _ _ _ _ H).
          - now apply (forget_eqterm _ _ _ _ H0).
          - now apply (forget_isterm _ _ _ i).
          - now apply (forget_isterm _ _ _ i0).
          - now apply (forget_isterm _ _ _ i1).
          - now apply (forget_isterm _ _ _ i2).
        }

    }

  (* forget_eqsubst *)
  - admit.
Defined.

End Translation.

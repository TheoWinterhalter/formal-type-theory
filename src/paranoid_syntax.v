(* Paranoid Syntax

   We propose an implementation of syntax that corresponds to the syntax with
   which this library was designed at first.
   It features all the specifics of the language as mutual inductive types.

   This includes explicit substitutions, seperate syntaxes for types and terms,
   optional Tarski universes and so on...

   This syntax is still configurable. For instance, if you decide not to have
   the Unit type as part of your theory, it will still be part of the syntax,
   but you won't be able to derive that [Γ ⊢ Unit] type or [Γ ⊢ unit : Unit].
*)

Require config tt wfconfig.

Section ParanoidSyntax.

Context {ConfigPrecond : config.Precond}.
Context {ConfigReflection : config.Reflection}.
Context {ConfigSimpleProducts : config.SimpleProducts}.
Context {ConfigProdEta : config.ProdEta}.
Context {ConfigUniverses : config.Universes}.
Context {ConfigWithProp : config.WithProp}.
Context {ConfigWithJ : config.WithJ}.
Context {ConfigEmpty : config.WithEmpty}.
Context {ConfigUnit : config.WithUnit}.
Context {ConfigBool : config.WithBool}.
Context {ConfigPi : config.WithPi}.
Local Instance hasExplicitSubstitutions : config.ExplicitSubstitutions
  := {| config.explicitsubstFlag := config.Yes |}.

(* universe levels *)
Inductive level : Type :=
| uni : nat -> level
| prop : level
.

Inductive context : Type :=
     | ctxempty : context
     | ctxextend : context -> type -> context

with type : Type :=
     | Prod : type -> type -> type
     | Id : type -> term -> term -> type
     | Subst : type -> substitution -> type
     | Empty : type
     | Unit : type
     | Bool : type
     | SimProd : type -> type -> type
     | Uni : level -> type
     | El : level -> term -> type

with term : Type :=
     | var : nat -> term
     | lam : type -> type -> term -> term
     | app : term -> type -> type -> term -> term
     | refl : type -> term -> term
     | j : type -> term -> type -> term -> term -> term -> term
     | subst : term -> substitution -> term
     | exfalso : type -> term -> term
     | unit : term
     | true : term
     | false : term
     | cond : type -> term -> term -> term -> term
     | pair : type -> type -> term -> term -> term
     | proj1 : type -> type -> term -> term
     | proj2 : type -> type -> term -> term
     | uniProd : level -> level -> term -> term -> term
     | uniId : level -> term -> term -> term -> term
     | uniEmpty : level -> term
     | uniUnit : level -> term
     | uniBool : nat -> term
     | uniSimProd : level -> level -> term -> term -> term
     | uniUni : level -> term

with substitution : Type :=
     | sbzero : type -> term -> substitution
     | sbweak : type -> substitution
     | sbshift : type -> substitution -> substitution
     | sbid : substitution
     | sbcomp : substitution -> substitution -> substitution
.

Definition exactly : forall {F A}, A -> config.Flag F -> A :=
  fun {F A} a f => a.

Local Instance Syntax : config.Syntax := {|
  config.context      := context ;
  config.type         := type ;
  config.term         := term ;
  config.substitution := substitution ;
  config.level        := level ;

  config.uni  := exactly uni ;
  config.prop := exactly prop ;

  config.ctxempty  := ctxempty ;
  config.ctxextend := ctxextend ;

  config.Prod    := exactly Prod ;
  config.Id      := Id ;
  config.Subst   := Subst ;
  config.Empty   := exactly Empty ;
  config.Unit    := exactly Unit ;
  config.Bool    := exactly Bool ;
  config.SimProd := exactly SimProd ;
  config.Uni     := exactly Uni ;
  config.El      := exactly El  ;

  config.var        := var ;
  config.lam        := exactly lam ;
  config.app        := exactly app ;
  config.refl       := refl ;
  config.j          := exactly j ;
  config.subst      := subst ;
  config.exfalso    := exactly exfalso ;
  config.unit       := exactly unit ;
  config.true       := exactly true  ;
  config.false      := exactly false ;
  config.cond       := exactly cond ;
  config.pair       := exactly pair ;
  config.proj1      := exactly proj1 ;
  config.proj2      := exactly proj2 ;
  config.uniProd    := exactly (exactly uniProd) ;
  (* config.uniId      := exactly (exactly uniId) ; *)
  config.uniId      := exactly uniId ;
  config.uniEmpty   := exactly (exactly uniEmpty) ;
  config.uniUnit    := exactly (exactly uniUnit) ;
  config.uniBool    := exactly (exactly uniBool) ;
  config.uniSimProd := exactly (exactly uniSimProd) ;
  config.uniUni     := exactly uniUni ;

  config.sbzero  := sbzero ;
  config.sbweak  := sbweak ;
  config.sbshift := sbshift ;
  config.sbid    := sbid ;
  config.sbcomp  := sbcomp
|}.

Definition isctx := tt.isctx.
Definition issubst := tt.issubst.
Definition istype := tt.istype.
Definition isterm := tt.isterm.
Definition eqctx := tt.eqctx.
Definition eqsubst := tt.eqsubst.
Definition eqtype := tt.eqtype.
Definition eqterm := tt.eqterm.

(* The fact that we need that would be in favor of not having Flag I guess. *)
Local Instance ESFlag : config.Flag config.explicitsubstFlag :=
  {| config.flagProof := config.yes |}.

Local Instance AdmissibleRules : wfconfig.AdmissibleRules := {
  TySubst := fun G D A sbs => tt._TySubst _ ;
  TermSubst := fun G D A u sbs => tt._TermSubst _ ;
  SubstRefl := fun G D sbs => tt._SubstRefl _ ;
  SubstSym := fun G D sbs sbt => tt._SubstSym _ ;
  SubstTrans := fun G D sb1 sb2 sb3 => tt._SubstTrans _ ;
  CongSubstZero := fun G A1 A2 u1 u2 => tt._CongSubstZero _ ;
  CongSubstWeak := fun G A1 A2 => tt._CongSubstWeak _ ;
  CongSubstShift := fun G D A1 A2 sbs1 sbs2 => tt._CongSubstShift _ ;
  CongSubstComp := fun G D E sbs1 sbs2 sbt1 sbt2 => tt._CongSubstComp _ ;
  EqSubstCtxConv := fun G1 G2 D1 D2 sbs sbt => tt._EqSubstCtxConv _ ;
  CompAssoc := fun G D E F sbs sbt sbr => tt._CompAssoc _ ;
  WeakNat := fun G D A sbs => tt._WeakNat _ ;
  WeakZero := fun G A u => tt._WeakZero _ ;
  ShiftZero := fun G D A u sbs => tt._ShiftZero _ ;
  CompShift := fun G D E A sbs sbt => tt._CompShift _ ;
  CompIdRight := fun G D sbs => tt._CompIdRight _ ;
  CompIdLeft := fun G D sbs => tt._CompIdLeft _ ;
  EqTySubstComp := fun G D E A sbs sbt => tt._EqTySubstComp _ ;
  EqTySubstProd := fun _ G D A B sbs => tt._EqTySubstProd _ _ ;
  EqTySubstId := fun G D A u v sbs => tt._EqTySubstId _ ;
  EqTySubstEmpty := fun _ G D sbs => tt._EqTySubstEmpty _ _ ;
  EqTySubstUnit := fun _ G D sbs => tt._EqTySubstUnit _ _ ;
  EqTySubstBool := fun _ G D sbs => tt._EqTySubstBool _ _ ;
  CongTySubst := fun G D A B sbs sbt => tt._CongTySubst _ ;
  EqTySubstSimProd := fun _ G D A B sbs => tt._EqTySubstSimProd _ _ ;
  EqTySubstUni := fun _ G D n sbs => tt._EqTySubstUni _ _ ;
  ElSubst := fun _ G D a n sbs => tt._ElSubst _ _ ;
  EqIdSubst := fun G A u => tt._EqIdSubst _ ;
  EqSubstComp := fun G D E A u sbs sbt => tt._EqSubstComp _ ;
  EqSubstWeak := fun G A B k => tt._EqSubstWeak _ ;
  EqSubstZeroZero := fun G u A => tt._EqSubstZeroZero _ ;
  EqSubstZeroSucc := fun G A B u k => tt._EqSubstZeroSucc _ ;
  EqSubstShiftZero := fun G D A sbs => tt._EqSubstShiftZero _ ;
  EqSubstShiftSucc := fun G D A B sbs k => tt._EqSubstShiftSucc _ ;
  EqSubstAbs := fun _ G D A B u sbs => tt._EqSubstAbs _ _ ;
  EqSubstApp := fun _ G D A B u v sbs => tt._EqSubstApp _ _ ;
  EqSubstRefl := fun G D A u sbs => tt._EqSubstRefl _ ;
  EqSubstJ := fun _ G D A C u v w p sbs => tt._EqSubstJ _ _ ;
  EqSubstExfalso := fun _ G D A u sbs => tt._EqSubstExfalso _ _ ;
  EqSubstUnit := fun _ G D sbs => tt._EqSubstUnit _ _ ;
  EqSubstTrue := fun _ G D sbs => tt._EqSubstTrue _ _ ;
  EqSubstFalse := fun _ G D sbs => tt._EqSubstFalse _ _ ;
  EqSubstCond := fun _ G D C u v w sbs => tt._EqSubstCond _ _ ;
  CongTermSubst := fun G D A u1 u2 sbs sbt => tt._CongTermSubst _ ;
  EqSubstPair := fun _ G D A B u v sbs => tt._EqSubstPair _ _ ;
  EqSubstProjOne := fun _ G D A B p sbs => tt._EqSubstProjOne _ _ ;
  EqSubstProjTwo := fun _ G D A B p sbs => tt._EqSubstProjTwo _ _ ;
  EqSubstUniProd := fun _ _ G D a b n m sb => tt._EqSubstUniProd _ _ _ ;
  EqSubstUniProdProp := fun _ _ _ G D a b l sbs => tt._EqSubstUniProdProp _ _ _ _ ;
  EqSubstUniId := fun _ G D a u v n sbs => tt._EqSubstUniId _ _ ;
  EqSubstUniEmpty := fun _ _ G D n sbs => tt._EqSubstUniEmpty _ _ _ ;
  EqSubstUniUnit := fun _ _ G D n sbs => tt._EqSubstUniUnit _ _ _ ;
  EqSubstUniBool := fun _ _ G D n sbs => tt._EqSubstUniBool _ _ _ ;
  EqSubstUniSimProd := fun _ _ G D a b n m sbs => tt._EqSubstUniSimProd _ _ _ ;
  EqSubstUniSimProdProp :=
    fun _ _ _ G D a b sbs => tt._EqSubstUniSimProdProp _ _ _ _ ;
  EqSubstUniUni := fun _ G D n sbs => tt._EqSubstUniUni _ _ ;
  EqSubstUniProp := fun _ _ G D sbs => tt._EqSubstUniProp _ _ _
}.

End ParanoidSyntax.

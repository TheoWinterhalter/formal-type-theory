(* Abstract notion of syntax. *)

(* Universe levels *)
Inductive level : Type :=
| uni : nat -> level
| prop : level
.

Class CONS A B := _sbcons : A -> B -> B.
Notation "u ⋅ σ" := (_sbcons u σ) (at level 20, right associativity).

Class SUBST substitution tt :=
  _subst : tt -> substitution -> tt.
Notation "t [ σ ]" := (_subst t σ) (at level 4).

Class EXTEND A B := _extend : A -> B -> A.
Notation "Γ , A" := (_extend Γ A) (at level 19, left associativity).

Section SyntaxDefinition.

Class Syntax := {
  context : Type;
  type : Type;
  term : Type;

  ctxempty : context;
  ctxextend :> EXTEND context type;

  Prod : type -> type -> type;
  Id : type -> term -> term -> type;
  Empty : type;
  Unit : type;
  Bool : type;
  BinaryProd : type -> type -> type;
  Uni : level -> type;
  El : level -> term -> type;

  var : nat -> term;
  lam : type -> type -> term -> term;
  app : term -> type -> type -> term -> term;
  refl : type -> term -> term;
  j : type -> term -> type -> term -> term -> term -> term;
  exfalso : type -> term -> term;
  unit : term;
  true : term;
  false : term;
  cond : type -> term -> term -> term -> term;
  pair : type -> type -> term -> term -> term;
  proj1 : type -> type -> term -> term;
  proj2 : type -> type -> term -> term;
  uniProd : level -> level -> term -> term -> term;
  uniId : level -> term -> term -> term -> term;
  uniEmpty : level -> term;
  uniUnit : level -> term;
  uniBool : nat -> term;
  uniBinaryProd : level -> level -> term -> term -> term;
  uniUni : level -> term;

  (* Substitutions *)
  substitution : Type;

  Subst :> SUBST substitution type;
  subst :> SUBST substitution term;

  sbid : substitution;
  sbcons :> CONS term substitution;
  sbweak : substitution;

  (* Computation of substitutions *)
  sbidterm :
    forall {t}, t[sbid] = t;
  sbidtype :
    forall {T}, T[sbid] = T;
  sbconszero :
    forall {σ u}, (var 0)[u ⋅ σ] = u;
  sbconssucc :
    forall {σ u n}, (var (S n))[u ⋅ σ] = (var n)[σ];
  sbweakvar :
    forall {n}, (var n)[sbweak] = var (S n);

  (* Action of substitutions *)
  SubstProd :
    forall {σ A B},
      (Prod A B)[σ] = Prod A[σ] B[(var 0) ⋅ σ];
  SubstId :
    forall {σ A u v},
      (Id A u v)[σ] = Id A[σ] u[σ] v[σ];
  SubstEmpty :
    forall {σ}, Empty[σ] = Empty;
  SubstUnit :
    forall {σ}, Unit[σ] = Unit;
  SubstBool :
    forall {σ}, Bool[σ] = Bool;
  SubstBinaryProd :
    forall {σ A B},
      (BinaryProd A B)[σ] = BinaryProd A[σ] B[σ];
  SubstUni :
    forall {σ l},
      (Uni l)[σ] = Uni l;
  SubstEl :
    forall {σ l a},
      (El l a)[σ] = El l a[σ];

  substLam :
    forall {σ A B t},
      (lam A B t)[σ] = lam A[σ] B[σ] t[(var 0) ⋅ σ];
  substApp :
    forall {σ A B u v},
      (app u A B v)[σ] = app u[σ] A[σ] B[σ] v[σ];
  substRefl :
    forall {σ A u},
      (refl A u)[σ] = refl A[σ] u[σ];
  substJ :
    forall {σ A u C w v p},
      (j A u C w v p)[σ] =
      j A[σ] u[σ] C[var 0 ⋅ var 0 ⋅ σ] w[σ] v[σ] p[σ];
  substExfalso :
    forall {σ A u},
      (exfalso A u)[σ] = exfalso A[σ] u[σ];
  substUnit :
    forall {σ}, unit[σ] = unit;
  substTrue :
    forall {σ}, true[σ] = true;
  substFalse :
    forall {σ}, false[σ] = false;
  substCond :
    forall {σ C u v w},
      (cond C u v w)[σ] = cond C[var 0 ⋅ σ] u[σ] v[σ] w[σ];
  substPair :
    forall {σ A B u v},
      (pair A B u v)[σ] = pair A[σ] B[σ] u[σ] v[σ];
  substProjOne :
    forall {σ A B p},
      (proj1 A B p)[σ] = proj1 A[σ] B[σ] p[σ];
  substProjTwo :
    forall {σ A B p},
      (proj2 A B p)[σ] = proj2 A[σ] B[σ] p[σ];
  substUniProd :
    forall {σ l1 l2 a b},
      (uniProd l1 l2 a b)[σ] =
      uniProd l1 l2 a[σ] b[var 0 ⋅ σ];
  substUniId :
    forall {σ l a u v},
      (uniId l a u v)[σ] = uniId l a[σ] u[σ] v[σ];
  substUniEmpty :
    forall {σ l}, (uniEmpty l)[σ] = uniEmpty l;
  substUniUnit :
    forall {σ l}, (uniUnit l)[σ] = uniUnit l;
  substUniBool :
    forall {σ l}, (uniBool l)[σ] = uniBool l;
  substUniBinaryProd :
    forall {σ l1 l2 a b},
      (uniBinaryProd l1 l2 a b)[σ] = uniBinaryProd l1 l2 a[σ] b[σ];
  substUniUni :
    forall {σ l}, (uniUni l)[σ] = uniUni l;

  Arrow := fun (A B :  type) => Prod A B[sbweak]
}.

Class TypeTheory (S : Syntax) := {
  _isctx : context -> Type;
  _istype : context -> type -> Type;
  _isterm : context -> term -> type -> Type;
  _eqctx : context -> context -> Type;
  _eqtype : context -> type -> type -> Type;
  _eqterm : context -> term -> term -> type -> Type
}.

Class SubstitutionTyping (S : Syntax) (T : TypeTheory S) := {
  (* Typing of substitutions *)
  issubst : substitution -> context -> context -> Type;

  SubstSbid : forall {Γ}, _isctx Γ -> issubst sbid Γ Γ;
  SubstWeak : forall {Γ A}, _isctx Γ -> _istype Γ A -> issubst sbweak (Γ,A) Γ;
  SubstCtxConv :
    forall {σ Γ Δ Δ'},
      _eqctx Δ' Δ ->
      issubst σ Γ Δ ->
      issubst σ Γ Δ';
  SubstCons :
    forall {σ u Γ Δ A},
      issubst σ Γ Δ ->
      _istype Δ A ->
      _isterm Γ u A[σ] ->
      issubst (u ⋅ σ) Γ (Δ, A);

  TySubst :
    forall {σ Γ Δ A},
      issubst σ Γ Δ ->
      _istype Δ A ->
      _istype Γ A[σ];
  TermSubst :
    forall {σ Γ Δ A u},
      issubst σ Γ Δ ->
      _istype Δ A ->
      _isterm Δ u A ->
      _isterm Γ u[σ] A[σ]
}.

End SyntaxDefinition.

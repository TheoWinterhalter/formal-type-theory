(* Universe levels *)
Inductive level : Type :=
| uni : nat -> level
| prop : level
.

Class CONS A B := _sbcons : A -> B -> B.
Notation "u ⋅ σ" := (_sbcons u σ) (at level 20, right associativity).

Class DROP substitution := _sbdrop : substitution -> substitution.
Notation "σ ↑" := (_sbdrop σ) (at level 3).

Class SUBST_TYPE substitution type :=
  _Subst : type -> substitution -> type.
Notation "A [ σ ]" := (_Subst A σ) (at level 4).

Class SUBST_TERM substitution term :=
  _subst : term -> substitution -> term.
Notation "t [ ← σ ]" := (_subst t σ) (at level 4).

Section SyntaxDefinition.

Class Syntax := {
  context : Type;
  type : Type;
  term : Type;
  substitution : Type;

  ctxempty : context;
  ctxextend : context -> type -> context;

  Subst :> SUBST_TYPE substitution type;

  Prod : type -> type -> type;
  Id : type -> term -> term -> type;
  Empty : type;
  Unit : type;
  Bool : type;
  BinaryProd : type -> type -> type;
  Uni : level -> type;
  El : level -> term -> type;


  subst :> SUBST_TERM substitution term;

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
  sbid : substitution;
  (* sbcons : term -> substitution -> substitution; *)
  sbcons :> CONS term substitution;
  (* Alternative:
     sbcons : term -> substitution -> substitution;
     sbcons' := (sbcons : CONS term substitution);
   *)
  sbweak : substitution;
  sbdrop :> DROP substitution;

  (* Computation of substitutions *)
  sbidterm :
    forall {t}, t[← sbid] = t;
  sbidtype :
    forall {T}, T[sbid] = T;
  sbconszero :
    forall {σ u}, (var 0)[← u ⋅ σ] = u;
  sbconssucc :
    forall {σ u n}, (var (S n))[← u ⋅ σ] = (var n)[← σ];
  sbweakvar :
    forall {n}, (var n)[← sbweak] = var (S n);
  sbdropvar :
    forall {σ n}, (var n)[← σ↑] = (var (S n))[← σ];

  (* Substitution extensionality principle *)
  sbext :
    forall {σ ρ},
      (forall n, (var n)[← σ] = (var n)[← ρ]) ->
      forall t, t[← σ] = t[← ρ];
  Sbext :
    forall {σ ρ},
      (forall n, (var n)[← σ] = (var n)[← ρ]) ->
      forall T, T[σ] = T[ρ];

  (* Action of substitutions *)
  SubstProd :
    forall {σ A B},
      (Prod A B)[σ] = Prod A[σ] B[(var 0) ⋅ σ];
  SubstId :
    forall {σ A u v},
      (Id A u v)[σ] = Id A[σ] u[← σ] v[← σ];
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
      (El l a)[σ] = El l a[← σ];

  substLam :
    forall {σ A B t},
      (lam A B t)[← σ] = lam A[σ] B[σ] t[← (var 0) ⋅ σ];
  substApp :
    forall {σ A B u v},
      (app u A B v)[← σ] = app u[← σ] A[σ] B[σ] v[← σ];
  substRefl :
    forall {σ A u},
      (refl A u)[← σ] = refl A[σ] u[← σ];
  substJ :
    forall {σ A u C w v p},
      (j A u C w v p)[← σ] =
      j A[σ] u[← σ] C[var 0 ⋅ var 0 ⋅ σ] w[← σ] v[← σ] p[← σ];
  substExfalso :
    forall {σ A u},
      (exfalso A u)[← σ] = exfalso A[σ] u[← σ];
  substUnit :
    forall {σ}, unit[← σ] = unit;
  substTrue :
    forall {σ}, true[← σ] = true;
  substFalse :
    forall {σ}, false[← σ] = false;
  substCond :
    forall {σ C u v w},
      (cond C u v w)[← σ] = cond C[var 0 ⋅ σ] u[← σ] v[← σ] w[← σ];
  substPair :
    forall {σ A B u v},
      (pair A B u v)[← σ] = pair A[σ] B[σ] u[← σ] v[← σ];
  substProjOne :
    forall {σ A B p},
      (proj1 A B p)[← σ] = proj1 A[σ] B[σ] p[← σ];
  substProjTwo :
    forall {σ A B p},
      (proj2 A B p)[← σ] = proj2 A[σ] B[σ] p[← σ];
  substUniProd :
    forall {σ l1 l2 a b},
      (uniProd l1 l2 a b)[← σ] =
      uniProd l1 l2 a[← σ] b[← var 0 ⋅ σ];
  substUniId :
    forall {σ l a u v},
      (uniId l a u v)[← σ] = uniId l a[← σ] u[← σ] v[← σ];
  substUniEmpty :
    forall {σ l}, (uniEmpty l)[← σ] = uniEmpty l;
  substUniUnit :
    forall {σ l}, (uniUnit l)[← σ] = uniUnit l;
  substUniBool :
    forall {σ l}, (uniBool l)[← σ] = uniBool l;
  substUniBinaryProd :
    forall {σ l1 l2 a b},
      (uniBinaryProd l1 l2 a b)[← σ] = uniBinaryProd l1 l2 a[← σ] b[← σ];
  substUniUni :
    forall {σ l}, (uniUni l)[← σ] = uniUni l;

  Arrow := fun (A B :  type) => Prod A B[sbweak]
}.

End SyntaxDefinition.

(* Notation "u ⋅ σ" := (sbcons u σ) (at level 20, right associativity). *)
(* Notation "A [ σ ]" := (Subst A σ) (at level 0). *)
(* Notation "t [ ← σ ]" := (subst t σ) (at level 0). *)
Notation "σ ~ ρ" := (forall n, (var n)[← σ] = (var n)[← ρ]) (at level 10).

Require Import Classes.CRelationClasses.

Instance sbextReflexive `{Syntax} : Reflexive (fun σ ρ => σ ~ ρ).
Proof.
  intros σ n. reflexivity.
Defined.

Instance sbextSymmetric `{Syntax} : Symmetric (fun σ ρ => σ ~ ρ).
Proof.
  intros σ ρ h n.
  symmetry. apply h.
Defined.

Instance sbextTransitive `{Syntax} : Transitive (fun σ ρ => σ ~ ρ).
Proof.
  intros σ ρ θ h1 h2 n.
  transitivity ((var n)[← ρ]).
  - apply h1.
  - apply h2.
Defined.
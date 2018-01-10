(* Handling meta-level substitutions. *)

Require Import Classes.CRelationClasses.

Require config.
Require Import config_tactics.
Require Import tt.
Require Import syntax.

(* Tactics to apply rules of substitutions *)

(* Rewrite G[t1] into G[t2] such that e solves t1 = t2 *)
Ltac context_rewrite G t1 t2 e :=
  let Gi := context G[t1] in
  let Gf := context G[t2] in
  replace Gi with Gf by (now rewrite e).

(* Ltac rewrite_Subst_action := *)
(*   first [ *)
(*     rewrite sbidtype *)
(*   | rewrite SubstProd *)
(*   | rewrite SubstId *)
(*   | rewrite SubstEmpty *)
(*   | rewrite SubstUnit *)
(*   | rewrite SubstBool *)
(*   | rewrite SubstBinaryProd *)
(*   | rewrite SubstUni *)
(*   | rewrite SubstEl *)
(*   ]. *)

Ltac rewrite_Subst_action :=
  match goal with
  | |- context G[ ?T[sbid] ] =>
    context_rewrite G T[sbid] T sbidtype

  | |- context G[ (Prod ?A ?B)[?σ] ] =>
    context_rewrite G (Prod A B)[σ] (Prod A[σ] B[var 0 ⋅ σ]) SubstProd

  | |- context G[ (Id ?A ?u ?v)[?σ] ] =>
    context_rewrite G (Id A u v)[σ] (Id A[σ] u[σ] v[σ]) SubstId

  | S : Syntax |- context G[ Empty[?σ] ] =>
    context_rewrite G Empty[σ] (@Empty S) SubstEmpty

  | S : Syntax |- context G[ Unit[?σ] ] =>
    context_rewrite G Unit[σ] (@Unit S) SubstUnit

  | S : Syntax |- context G[ Bool[?σ] ] =>
    context_rewrite G Bool[σ] (@Bool S) SubstBool

  | |- context G[ (BinaryProd ?A ?B)[?σ] ] =>
    context_rewrite G
                    (BinaryProd A B)[σ]
                    (BinaryProd A[σ] B[σ])
                    SubstBinaryProd

  | |- context G[ (Uni ?l)[?σ] ] =>
    context_rewrite G (Uni l)[σ] (Uni l) SubstUni

  | |- context G[ (El ?l ?a)[?σ] ] =>
    context_rewrite G (El l a)[σ] (El l a[σ]) SubstEl

  end.

Ltac rewrite_subst_action :=
  first [
    rewrite sbidterm
  | rewrite substLam
  | rewrite substApp
  | rewrite substRefl
  | rewrite substJ
  | rewrite substExfalso
  | rewrite substUnit
  | rewrite substTrue
  | rewrite substFalse
  | rewrite substCond
  | rewrite substPair
  | rewrite substProjOne
  | rewrite substProjTwo
  | rewrite substUniProd
  | rewrite substUniId
  | rewrite substUniEmpty
  | rewrite substUniUnit
  | rewrite substUniBool
  | rewrite substUniBinaryProd
  | rewrite substUniUni
  ].

Ltac smart_rewrite_subst_action :=
  match goal with
  | |- context G[ ?t[sbid] ] =>
    context_rewrite G t[sbid] t sbidterm

  | |- context G[ (lam ?A ?B ?t)[?σ] ] =>
    context_rewrite G
                    (lam A B t)[σ]
                    (lam A[σ] B[var 0 ⋅ σ] t[var 0 ⋅ σ])
                    substLam

  | |- context G[ (app ?u ?A ?B ?v)[?σ] ] =>
    context_rewrite G
                    (app u A B v)[σ]
                    (app u[σ] A[σ] B[var 0 ⋅ σ] v[σ])
                    substApp

  | |- context G[ (refl ?A ?u)[?σ] ] =>
    context_rewrite G (refl A u)[σ] (refl A[σ] u[σ]) substRefl

  | |- context G[ (j ?A ?u ?C ?w ?v ?p)[?σ] ] =>
    context_rewrite G
                    (j A u C w v p)[σ]
                    (j A[σ] u[σ] C[var 0 ⋅ var 0 ⋅ σ] w[σ] v[σ] p[σ])
                    substJ

  | |- context G[ (exfalso ?A ?u)[?σ] ] =>
    context_rewrite G (exfalso A u)[σ] (exfalso A[σ] u[σ]) substExfalso

  | S : Syntax |- context G[ unit[?σ] ] =>
    context_rewrite G unit[σ] (@unit S) substUnit

  | S : Syntax |- context G[ true[?σ] ] =>
    context_rewrite G true[σ] (@true S) substTrue

  | S : Syntax |- context G[ false[?σ] ] =>
    context_rewrite G false[σ] (@false S) substFalse

  | |- context G[ (cond ?C ?u ?v ?w)[?σ] ] =>
    context_rewrite G
                    (cond C u v w)[σ]
                    (cond C[var 0 ⋅ σ] u[σ] v[σ] w[σ])
                    substCond

  (* | |-  *)
  end.

Ltac rewrite_subst_var :=
  first [
    rewrite sbconszero
  | rewrite sbconssucc
  | rewrite sbweakvar
  ].

Ltac rewrite_subst :=
  first [
    rewrite_Subst_action
  | rewrite_subst_action
  | rewrite_subst_var
  ].

Ltac rewrite_substs :=
  repeat rewrite_subst.

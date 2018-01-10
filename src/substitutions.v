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

Ltac smart_rewrite_Subst_action :=
  lazymatch goal with
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

Ltac rewrite_Subst_action :=
  first [
    rewrite sbidtype
  | rewrite SubstProd
  | rewrite SubstId
  | rewrite SubstEmpty
  | rewrite SubstUnit
  | rewrite SubstBool
  | rewrite SubstBinaryProd
  | rewrite SubstUni
  | rewrite SubstEl
  ].

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

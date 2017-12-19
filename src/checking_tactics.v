(* Tactics and auxiliary lemmas for deriving judgments. *)

Require config.
Require Import config_tactics.
Require Import tt.
Require Import syntax.

(* Tactics to apply rules of substitutions *)

Ltac rewrite_Subst_action :=
  first [
    rewrite SubstProd
  | rewrite SubstId
  | rewrite SubstEmpty
  | rewrite SubstUnit
  | rewrite SubstBool
  | rewrite SubstBinaryProd
  | rewrite SubstUni
  | rewrite SubstEl
  | rewrite sbidtype
  ].

Ltac rewrite_subst_action :=
  first [
    rewrite substLam
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
  | rewrite sbidterm
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


(* Tactics to apply introduction rules of type theory. *)

Ltac isctxintrorule tac :=
  lazymatch goal with
  | |- isctx ctxempty => tac CtxEmpty
  | |- isctx (ctxextend ?Γ ?A) => tac CtxExtend
  | |- ?G => fail "Goal" G "isn't handled by tactic isctxintrorule"
  end.

Ltac istypeintrorule tac :=
  lazymatch goal with
  | |- istype ?Γ (Prod ?A ?B) => tac TyProd
  | |- istype ?Γ (Id ?A ?u ?v) => tac TyId
  | |- istype ?Γ Empty => tac TyEmpty
  | |- istype ?Γ Unit => tac TyUnit
  | |- istype ?Γ Bool => tac TyBool
  | |- istype ?Γ (BinaryProd ?A ?B) => tac TyBinaryProd
  | |- istype ?Γ (Uni ?l) => tac TyUni
  | |- istype ?Γ (El ?l ?a) => tac TyEl
  | |- ?G => fail "Goal" G "isn't handled by tactic istypeintrorule"
  end.

Ltac istermintrorule tac :=
  lazymatch goal with
  | |- isterm _ (var 0) _ => tac TermVarZero
  | |- isterm _ (var (S ?k)) _ => tac TermVarSucc
  | |- isterm _ (lam ?A ?B ?u) _ => tac TermAbs
  | |- isterm _ (app ?u ?A ?B ?v) _ => tac TermApp
  | |- isterm _ (refl ?A ?u) _ => tac TermRefl
  | |- isterm _ (j ?A ?u ?C ?w ?v ?p) _ => tac TermJ
  | |- isterm _ (exfalso ?A ?u) _ => tac TermExfalso
  | |- isterm _ unit _ => tac TermUnit
  | |- isterm _ true _ => tac TermTrue
  | |- isterm _ false _ => tac TermFalse
  | |- isterm _ (cond ?C ?u ?v ?w) _ => tac TermCond
  | |- isterm _ (pair ?A ?B ?u ?v) _ => tac TermPair
  | |- isterm _ (proj1 ?A ?B ?p) _ => tac TermProjOne
  | |- isterm _ (proj2 ?A ?B ?p) _ => tac TermProjTwo
  | |- isterm _ (uniProd (uni ?n) (uni ?m) ?a ?b) _ => tac TermUniProd
  | |- isterm _ (uniProd ?l prop ?a ?b) _ => tac TermUniProdProp
  | |- isterm _ (uniId ?n ?a ?u ?v) _ => tac TermUniId
  | |- isterm _ (uniEmpty ?l) _ => tac TermUniEmpty
  | |- isterm _ (uniUnit ?l) _ => tac TermUniUnit
  | |- isterm _ (uniBool ?n) _ => tac TermUniBool
  | |- isterm _ (uniBinaryProd (uni ?n) (uni ?m) ?a ?b) _ => tac TermUniBinaryProd
  | |- isterm _ (uniBinaryProd prop prop ?a ?b) _ => tac TermUniBinaryProdProp
  | |- isterm _ (uniUni (uni ?n)) _ => tac TermUniUni
  | |- isterm _ (uniUni prop) _ => tac TermUniProp
  | |- ?G => fail "Goal" G "isn't handled by tactic istermintrorule"
  end.

Ltac eqctxintrorule tac :=
  lazymatch goal with
  | |- eqctx ctxempty ctxempty => tac EqCtxEmpty
  | |- eqctx (ctxextend ?Γ ?A) (ctxextend ?Δ ?B) => tac EqCtxExtend
  | |- ?G => fail "Goal" G "isn't handled by tactic eqctxintrorule"
  end.

Ltac eqtypeintrorule tac :=
  lazymatch goal with
  | |- eqtype _ (Prod ?A ?B) (Prod ?C ?D) => tac CongProd
  | |- eqtype _ (Id ?A ?u ?v) (Id ?B ?w ?z) => tac CongId
  | |- eqtype _ Empty Empty => tac EqTyRefl
  | |- eqtype _ Unit Unit => tac EqTyRefl
  | |- eqtype _ Bool Bool => tac EqTyRefl
  | |- eqtype _ (BinaryProd ?A ?B) (BinaryProd ?C ?D) => tac CongBinaryProd
  | |- eqtype _ (Uni ?l) (Uni ?l') => tac EqTyRefl
  | |- eqtype _ (El ?l ?a) (El ?l' ?b) => tac CongEl
  | |- ?G => fail "Goal" G "isn't handled by tactic eqtypeintrorule"
  end.

Ltac eqtermintrorule tac :=
  lazymatch goal with
  | |- eqterm _ (var ?n) (var ?n) _ => tac EqRefl
  | |- eqterm _ (lam ?A ?B ?u) (lam ?C ?D ?v) _ => tac CongAbs
  | |- eqterm _ (app ?u ?A ?B ?v) (app ?w ?C ?D ?z) _ => tac CongApp
  | |- eqterm _ (refl ?A ?u) (refl ?B ?v) _ => tac CongRefl
  | |- eqterm _ (j ?A ?u ?C ?w ?v ?p) (j ?B ?x ?D ?z ?y ?q) _ => tac CongJ
  | |- eqterm _ (exfalso ?A ?u) (exfalso ?B ?v) _ => tac CongExfalso
  | |- eqterm _ unit unit _ => tac EqRefl
  | |- eqterm _ true true _ => tac EqRefl
  | |- eqterm _ false false _ => tac EqRefl
  | |- eqterm _ (cond ?C ?u ?v ?w) (cond ?D ?x ?y ?z) _ => tac CongCond
  | |- eqterm _ (pair ?A ?B ?u ?v) (pair ?C ?D ?w ?z) _ => tac CongPair
  | |- eqterm _ (proj1 ?A ?B ?p) (proj1 ?C ?D ?q) _ => tac CongProjOne
  | |- eqterm _ (proj2 ?A ?B ?p) (proj2 ?C ?D ?q) _ => tac CongProjTwo
  | |- eqterm _ (uniProd (uni _) (uni _) ?A ?B) (uniProd (uni _) (uni _) ?C ?D) _
    => tac CongUniProd
  | |- eqterm _ (uniProd ?l prop ?A ?B) (uniProd ?l' prop ?C ?D) _
    => tac CongUniProdProp
  | |- eqterm _ (uniId ?l ?A ?u ?v) (uniId ?l' ?B ?w ?z) _ => tac CongUniId
  | |- eqterm _ (uniEmpty ?l) (uniEmpty ?l') _ => tac EqRefl
  | |- eqterm _ (uniUnit ?l) (uniUnit ?l') _ => tac EqRefl
  | |- eqterm _ (uniBool ?n) (uniBool ?m) _ => tac EqRefl
  | |- eqterm _ (uniBinaryProd (uni _) (uni _) ?A ?B)
             (uniBinaryProd (uni _) (uni _) ?C ?D) _
      => tac CongUniBinaryProd
  | |- eqterm _ (uniBinaryProd prop prop ?A ?B) (uniBinaryProd prop prop ?C ?D) _
      => tac CongUniBinaryProdProp
  | |- eqterm _ (uniUni ?l) (uniUni ?l') _ => tac EqRefl
  | |- ?G => fail "Goal" G "isn't handled by tactic eqtermintrorule"
  end.

Ltac intro_rule apptac :=
  lazymatch goal with
  | |- isctx _ => isctxintrorule apptac
  | |- istype _ _ => istypeintrorule apptac
  | |- isterm _ _ _ => istermintrorule apptac
  | |- eqctx _ _ => eqctxintrorule apptac
  | |- eqtype _ _ _ => eqtypeintrorule apptac
  | |- eqterm _ _ _ _ => eqtermintrorule apptac
  end.

Ltac typeconversion :=
  lazymatch goal with
  | |- isterm ?Γ ?u ?A => ceapply TermTyConv
  | |- eqterm ?Γ ?u ?v ?A => ceapply EqTyConv
  | |- ?G => fail "Type conversion doesn't apply to goal" G
  end.

Ltac contextconversion :=
  lazymatch goal with
  | |- istype ?Γ ?A => ceapply TyCtxConv
  | |- isterm ?Γ ?u ?A => ceapply TermCtxConv
  | |- eqtype ?Γ ?A ?B => ceapply EqTyCtxConv
  | |- eqterm ?Γ ?u ?v ?A => ceapply EqCtxConv
  | |- ?G => fail "Context conversion doesn't apply to goal" G
  end.

Ltac unfold_syntax :=
  unfold CONS, SUBST_TYPE, SUBST_TERM, Arrow, _sbcons, _Subst, _subst in *.


(* Configuration options for the tactics. *)
Inductive check_doshelf := DoShelf | DontShelf.
Inductive check_debug := DoDebug | DontDebug.

Ltac do_shelf flag :=
  match flag with
  | DoShelf => idtac
  | DontShelf => fail "Cannot shelve"
  end.

Ltac do_debug flag :=
  match flag with
  | DoDebug => idtac
  | DontDebug => fail "Cannot debug"
  end.

Ltac myfail flag :=
  lazymatch goal with
  | |- ?G =>
    tryif (do_debug flag)
    then fail 1000 "Cannot solve subgoal" G
    else fail "Cannot solve subgoal" G
  | _ => fail 10000 "This shouldn't happen!"
  end.

Ltac myshelve debug shelf :=
  tryif (do_shelf shelf)
  then shelve
  else myfail debug.

(* Tactics for type checking. *)

Ltac preop :=
  doConfig ;
  unfold_syntax ;
  rewrite_substs.

(* The parameters are:
   - debug: Whether to display debug message when failing(?).
   - shelf: Whether to allow shelving.
   - apptac: Tactic to replace apply.
   - ktac: Continuation tactic.
 *)
Ltac check_step_factory debug shelf apptac ktac :=
  preop ;
  lazymatch goal with
  (* Context well-formedness *)
  | |- isctx ?Γ =>
    tryif (is_var Γ)
    (* If the context is a variable in scope, we try assumption. *)
    then first [
      (* TODO: Have this bit depend on whether we use echeck of check. *)
      assumption
    | myfail debug
    ]
    else tryif (is_evar Γ)
      (* If it is an existential variable, we shelve it to solve later. *)
      then myshelve debug shelf
      (* Otherwise, we try introduction rules. *)
      else first [
        isctxintrorule apptac
      | myfail debug
      ] ; ktac debug shelf apptac

  (* Type well-formedness *)
  | |- istype ?Γ ?A =>
    tryif (is_var A)
    then first [
      (* TODO: Have this bit depend on whether we use echeck of check. *)
      eassumption
    | contextconversion ; [ eassumption | .. ]
    | myfail debug
    ] ; ktac debug shelf apptac
    else tryif (is_evar A)
      then myshelve debug shelf
      else first [
        istypeintrorule apptac
      | myfail debug
      ] ; ktac debug shelf apptac

  (* Typing of terms *)
  | |- isterm ?Γ ?u ?A =>
    tryif (is_var u)
    then first [
      eassumption
    | typeconversion ; [ eassumption | .. ]
    | contextconversion ; [ eassumption | .. ]
    | contextconversion ; [
        typeconversion ; [ eassumption | .. ]
      | ..
      ]
    | myfail debug
    ] ; ktac debug shelf apptac
    else tryif (is_evar u)
      then myshelve debug shelf
      else first [
        istermintrorule apptac
      | typeconversion ; [ istermintrorule apptac | ..]
      | myfail debug
      ] ; ktac debug shelf apptac

  (* Equality of contexts *)
  | |- eqctx ?Γ ?Δ =>
    tryif (is_var Γ ; is_var Δ)
    then first [
      assumption
    | capply CtxSym ; [ assumption | .. ]
    | myfail debug
    ]
    else tryif (is_evar Γ || is_evar Δ)
      then myshelve debug shelf
      else first [
        eqctxintrorule apptac
      | apptac CtxSym ; [ eqctxintrorule apptac | .. ]
      | apptac CtxRefl
      | myfail debug
      ] ; ktac debug shelf apptac

  (* Equality of types *)
  | |- eqtype ?Γ ?A ?B =>
    tryif (is_var A ; is_var B)
    then first [
      eassumption
    | ceapply EqTyRefl
    | ceapply EqTySym ; [ eassumption | .. ]
    | contextconversion ; [
            first [
              eassumption
            | ceapply EqTySym ; [ eassumption | .. ]
            ]
          | ..
          ]
    | myfail debug
    ] ; ktac debug shelf apptac
    else tryif (is_evar A || is_evar B)
      then myshelve debug shelf
      else first [
        eqtypeintrorule apptac
      | apptac EqTySym ; [ eqtypeintrorule apptac | .. ]
      | apptac EqTyRefl
      | myfail debug
      ] ; ktac debug shelf apptac

  (* Equality of terms *)
  | |- eqterm ?Γ ?u ?v ?A =>
    tryif (is_var u ; is_var v)
    then first [
      eassumption
    | ceapply EqRefl
    | ceapply EqSym ; [ eassumption |.. ]
    | typeconversion ; [ eassumption | .. ]
    | typeconversion ; [
        ceapply EqSym ; [ eassumption | .. ]
      | ..
      ]
    | myfail debug
    ] ; ktac debug shelf apptac
    else tryif (is_evar u || is_evar v)
      then myshelve debug shelf
      else first [
        eqtermintrorule
      | apptac EqSym ; [ eqtermintrorule apptac | .. ]
      | typeconversion ; [ eqtermintrorule apptac | .. ]
      | typeconversion ; [
          apptac EqSym ; [ eqtermintrorule apptac | .. ]
        | ..
        ]
      | apptac EqRefl
      | myfail debug
      ] ; ktac debug shelf apptac

  (* Unknown goal *)
  | |- ?G => fail "Goal" G "isn't handled by tactic check_step_factory"
  end.

Ltac idktac debug shelf apptac := idtac.

Ltac check_step debug shelf apptac :=
  check_step_factory debug shelf apptac idktac.

Ltac check_f debug shelf apptac :=
  check_step_factory debug shelf apptac check_f.


(* Instances *)

Ltac app_capply X := capply X.
Ltac app_ceapply X := ceapply X.

Ltac introrule := intro_rule app_capply.
Ltac eintrorule := intro_rule app_ceapply.

Ltac checkstep := check_step DoDebug DoShelf app_capply.
Ltac echeckstep := check_step DoDebug DoShelf app_ceapply.

Ltac check := check_f DoDebug DoShelf app_capply.
Ltac echeck := check_f DoDebug DoShelf app_ceapply.
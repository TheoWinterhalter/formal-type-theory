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

(* TODO Maybe handle the case "isctx ?Γ" and evars.
   Fail, debug and shelf as well.
 *)
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

Ltac unfold_syntax :=
  unfold CONS, SUBST_TYPE, SUBST_TERM, Arrow, _sbcons, _Subst, _subst in *.


(* Tactics for type checking. *)

Ltac preop :=
  unfold_syntax ;
  rewrite_substs.

Ltac check_step_factory apptac ktac :=
  preop ;
  lazymatch goal with
  | |- isctx ?Γ => isctxintrorule apptac ; ktac apptac
  | |- istype ?Γ ?A => istypeintrorule apptac ; ktac apptac
  | |- isterm ?Γ ?u ?A => istermintrorule apptac ; ktac apptac
  | |- ?G => fail "Goal" G "isn't handled by tactic check_step_factory"
  end.

Ltac idktac apptac := idtac.

Ltac check_step apptac :=
  check_step_factory apptac idktac.

Ltac check_f apptac :=
  check_step_factory apptac check_f.


(* Instances *)

Ltac app_capply X := capply X.
Ltac app_ceapply X := ceapply X.

Ltac checkstep := check_step app_capply.
Ltac echeckstep := check_step app_ceapply.

Ltac check := check_f app_capply.
Ltac echeck := check_f app_ceapply.

(*! OLD BELOW !*)

(* Configuration options for the tactics. *)
Inductive magic_try := DoTry | DontTry.
Inductive magic_doshelf := DoShelf | DontShelf.
Inductive magic_dotysym := DoTysym | DontTysym.
Inductive magic_doeqsym := DoEqsym | DontEqsym.
Inductive macic_debug := DoDebug | DontDebug.


Ltac do_try flag :=
  match flag with
  | DoTry => idtac
  | DontTry => fail "Cannot try"
  end.

Ltac do_shelf flag :=
  match flag with
  | DoShelf => idtac
  | DontShelf => fail "Cannot shelve"
  end.

Ltac do_tysym flag :=
  match flag with
  | DoTysym => idtac
  | DontTysym => fail "Cannot do TySym"
  end.

Ltac do_eqsym flag :=
  match flag with
  | DoEqsym => idtac
  | DontEqsym => fail "Cannot do EqSym"
  end.

Ltac do_debug flag :=
  match flag with
  | DoDebug => idtac
  | DontDebug => fail "Cannot debug"
  end.

(* Checking if we're dealing with a suitable goal. *)
(* This would be interesting in another file maybe? *)
Ltac check_goal :=
  doConfig ;
  lazymatch goal with
  | |- isctx ?G => idtac
  | |- istype ?G ?A => idtac
  | |- isterm ?G ?u ?A => idtac
  | |- eqctx ?G ?D => idtac
  | |- eqtype ?G ?A ?B => idtac
  | |- eqterm ?G ?u ?v ?A => idtac
  | |- ?G => fail "Goal" G " is not a goal meant to be handled by magic."
  end.

(* My own tactic to fail with the goal information. *)
Ltac myfail flag :=
  lazymatch goal with
  | |- ?G =>
    tryif (do_debug flag)
    then fail 1000 "Cannot solve subgoal" G
    else fail "Cannot solve subgoal" G
  | _ => fail "This shouldn't happen!"
  end.

(* Factorizing some cases *)
Ltac eqtype_subst G A sbs B k try shelf tysym debug :=
  fail "No longer supported!".

(* Magic Tactic *)
(* It is basically a type checker that doesn't do the smart things,
   namely type and context conversions (and it doesn't rely on reflection
   obviously). *)
Ltac magicn try shelf tysym debug :=
  doConfig ;
  (* We only ever apply magic to suitable goals *)
  check_goal ;
  first [
    assumption (* Why can't I remove it? *)
  | (* We have several things we need to do to the tactic:
       * Remove the _ case.
       * Add a token to solve equalities with only one side as reflexivity.
         (Maybe shelve them in the meantime?)
       * We can take advantage of the information we have at hand on
         substitutions to make magic finer!
     *)
    lazymatch goal with
    (*! Contexts !*)
    | |- isctx ctxempty =>
      capply CtxEmpty
    | |- isctx (ctxextend ?G ?A) =>
      ceapply CtxExtend ; magicn try shelf DoTysym debug
    | |- isctx ?G =>
      tryif (is_var G)
      then first [
        assumption
      | myfail debug
      ]
      else tryif (do_shelf shelf)
        then shelve
        else myfail debug

    (*! Types !*)
    | |- istype ?G (Prod ?A ?B) =>
      first [
        ceapply TyProd
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- istype ?G (Id ?A ?u ?v) =>
      first [
        ceapply TyId
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- istype ?G Empty =>
      first [
        ceapply TyEmpty
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- istype ?G Unit =>
      first [
        ceapply TyUnit
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- istype ?G Bool =>
      first [
        ceapply TyBool
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- istype ?G (BinaryProd ?A ?B) =>
      first [
        ceapply TyBinaryProd
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- istype ?G (Uni ?n) =>
      first [
        ceapply TyUni
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- istype ?G (El ?l ?a) =>
      first [
        ceapply TyEl
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- istype ?G ?A =>
      tryif (is_var A)
      then first [
        eassumption
      | ceapply TyCtxConv ; [ eassumption | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
      else tryif (do_shelf shelf)
        then shelve
        else myfail debug

    (*! Terms !*)
    | |- isterm (ctxextend ?G ?A) (var 0) ?T =>
      first [
        ceapply TermVarZero
      | ceapply TermTyConv ; [ ceapply TermVarZero | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm (ctxextend ?G ?B) (var (S ?k)) ?A =>
      first [
        ceapply TermVarSucc
      | ceapply TermTyConv ; [ ceapply TermVarSucc | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (var ?k) ?A =>
      (* In that case, we might shelve, if the don't know the context. *)
      tryif (is_evar G)
      then shelve
      else first [
        eassumption
      | myfail debug
      ]
    | |- isterm ?G (lam ?A ?B ?u) ?C =>
      first [
        ceapply TermAbs
      | ceapply TermTyConv ; [ ceapply TermAbs | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (app ?u ?A ?B ?v) ?C =>
      first [
        ceapply TermApp
      | ceapply TermTyConv ; [ ceapply TermApp | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (refl ?A ?u) ?B =>
      first [
        ceapply TermRefl
      | ceapply TermTyConv ; [ ceapply TermRefl | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (j ?A ?u ?C ?w ?v ?p) ?T =>
      first [
        ceapply TermJ
      | ceapply TermTyConv ; [ ceapply TermJ | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (exfalso ?A ?u) _ =>
      first [
        ceapply TermExfalso
      | ceapply TermTyConv ; [ ceapply TermExfalso | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G unit ?A =>
      first [
        ceapply TermUnit
      | ceapply TermTyConv ; [ ceapply TermUnit | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G true ?A =>
      first [
        ceapply TermTrue
      | ceapply TermTyConv ; [ ceapply TermTrue | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G false ?A =>
      first [
        ceapply TermFalse
      | ceapply TermTyConv ; [ ceapply TermFalse | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (cond ?C ?u ?v ?w) ?T =>
      first [
        ceapply TermCond
      | ceapply TermTyConv ; [ ceapply TermCond | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (pair ?A ?B ?u ?v) ?T =>
      first [
        ceapply TermPair
      | ceapply TermTyConv ; [ ceapply TermPair | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (proj1 ?A ?B ?p) ?T =>
      first [
        ceapply TermProjOne
      | ceapply TermTyConv ; [ ceapply TermProjOne | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (proj2 ?A ?B ?p) ?T =>
      first [
        ceapply TermProjTwo
      | ceapply TermTyConv ; [ ceapply TermProjTwo | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (uniProd ?l prop ?a ?b) ?T =>
      first [
        ceapply TermUniProdProp
      | ceapply TermTyConv ; [ ceapply TermUniProdProp | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (uniProd ?n ?m ?a ?b) ?T =>
      first [
        ceapply TermUniProd
      | ceapply TermTyConv ; [ ceapply TermUniProd | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (uniId ?n ?a ?u ?v) ?T =>
      first [
        ceapply TermUniId
      | ceapply TermTyConv ; [ ceapply TermUniId | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (uniEmpty ?n) ?T =>
      first [
        ceapply TermUniEmpty
      | ceapply TermTyConv ; [ ceapply TermUniEmpty | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (uniUnit ?n) ?T =>
      first [
        ceapply TermUniUnit
      | ceapply TermTyConv ; [ ceapply TermUniUnit | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (uniBool ?n) ?T =>
      first [
        ceapply TermUniBool
      | ceapply TermTyConv ; [ ceapply TermUniBool | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (uniBinaryProd prop prop ?a ?b) ?T =>
      first [
        ceapply TermUniBinaryProdProp
      | ceapply TermTyConv ; [ ceapply TermUniBinaryProdProp | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (uniBinaryProd ?n ?m ?a ?b) ?T =>
      first [
        ceapply TermUniBinaryProd
      | ceapply TermTyConv ; [ ceapply TermUniBinaryProd | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (uniUni prop) ?T =>
      first [
        ceapply TermUniProp
      | ceapply TermTyConv ; [ ceapply TermUniProp | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- isterm ?G (uniUni ?n) ?T =>
      first [
        ceapply TermUniUni
      | ceapply TermTyConv ; [ ceapply TermUniUni | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | [ H : isterm ?G ?v ?A, H' : isterm ?G ?v ?B |- isterm ?G ?v ?C ] =>
      (* We have several options so we don't take any risk. *)
      (* Eventually this should go away. I don't want to do the assert thing
         anymore. *)
      first [
        is_var A ; exact H
      | is_var B ; exact H'
      | do_shelf shelf ; shelve
      ]
    | |- isterm ?G ?u ?A =>
      tryif (is_evar u)
      (* If u is an existential variable we don't touch it. *)
      then tryif (do_shelf shelf)
        then shelve
        else myfail debug
      else (
        tryif (is_var u)
        then first [
          eassumption
        | ceapply TermTyConv ; [ eassumption | .. ]
        | ceapply TermCtxConv ; [ eassumption | .. ]
        | ceapply TermCtxConv ; [
            ceapply TermTyConv ; [ eassumption | .. ]
          | ..
          ]
        | myfail debug
        ] ; magicn try shelf DoTysym debug
        else tryif (do_shelf shelf)
          then shelve
          else myfail debug
      )

    (*! Equality of contexts !*)
    | |- eqctx ctxempty ctxempty =>
      capply EqCtxEmpty
    | |- eqctx (ctxextend ?G ?A) (ctxextend ?D ?B) =>
      first [
        ceapply EqCtxExtend
      | capply CtxSym ; [ ceapply EqCtxExtend | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqctx ?G ?G =>
      first [
        ceapply CtxRefl
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqctx ?G ?D =>
      tryif (is_var G ; is_var D)
      then first [
        assumption
      | capply CtxSym ; [ assumption | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
      else tryif (do_shelf shelf)
        then shelve
        else myfail debug

    (*! Equality of types !*)
    | |- eqtype ?G (Id ?A ?u ?v) (Id ?B ?w ?z) =>
      first [
        ceapply CongId
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqtype ?G (Prod ?A ?B) (Prod ?C ?D) =>
      first [
        ceapply CongProd
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqtype ?G Unit Unit =>
      first [
        ceapply EqTyRefl
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqtype ?G Bool Bool =>
      first [
        ceapply EqTyRefl
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqtype ?G (BinaryProd _ _) (BinaryProd _ _) =>
      first [
        ceapply CongBinaryProd
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqtype ?G (Uni _) (Uni _) =>
      first [
        ceapply EqTyRefl
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqtype ?G (El ?l ?a) (El ?l' ?b) =>
      first [
        ceapply CongEl
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqtype ?G ?A ?B =>
      tryif (is_var A ; is_var B)
      then (
        first [
          eassumption
        | ceapply EqTyRefl
        | ceapply EqTySym ; [ eassumption | .. ]
        | ceapply EqTyCtxConv ; [
            first [
              eassumption
            | ceapply EqTySym ; [ eassumption | .. ]
            ]
          | ..
          ]
        | myfail debug
        ] ; magicn try shelf DoTysym debug
      )
      else tryif (is_evar A || is_evar B)
        then tryif (do_shelf shelf)
          then shelve
          else myfail debug
        else myfail debug

    (*! Equality of terms !*)
    | |- eqterm ?G ?u ?u ?A =>
      first [
        ceapply EqRefl
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G ?u ?v Empty =>
      first [
        config eapply @EqTermExfalso with (w := u)
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G ?u ?v Unit =>
      first [
        ceapply UnitEta
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    (* Where should ProdBeta be handled? *)
    (* Same for CondTrue, CondFalse, JRefl *)
    (* ProdEta should come in after CongApp and CongProd probably *)
    | |- eqterm ?G (lam ?A1 ?A2 ?u1) (lam ?B1 ?B2 ?u2) _ =>
      first [
        ceapply CongAbs
      | ceapply EqTyConv ; [ ceapply CongAbs | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (app ?u1 ?A1 ?A2 ?u2) (app ?v1 ?B1 ?B2 ?v2) _ =>
      first [
        ceapply CongApp
      | ceapply EqTyConv ; [ ceapply CongApp | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (refl ?A1 ?u1) (refl ?A2 ?u2) _ =>
      first [
        ceapply CongRefl
      | ceapply EqTyConv ; [ ceapply CongRefl | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (j ?A1 ?u1 ?C1 ?w1 ?v1 ?p1) (j ?A2 ?u2 ?C2 ?w2 ?v2 ?p2) _ =>
      first [
        ceapply CongJ
      | ceapply EqTyConv ; [ ceapply CongJ | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (cond ?C1 ?u1 ?v1 ?w1) (cond ?C2 ?u2 ?v2 ?w2) _ =>
      first [
        ceapply CongCond
      | ceapply EqTyConv ; [ ceapply CongCond | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (pair _ _ _ _) (pair _ _ _ _) _ =>
      first [
        ceapply CongPair
      | ceapply EqTyConv ; [ ceapply CongPair | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (proj1 _ _ _ ) (proj1 _ _ _) _ =>
      first [
        ceapply CongProjOne
      | ceapply EqTyConv ; [ ceapply CongProjOne | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (proj2 _ _ _ ) (proj2 _ _ _) _ =>
      first [
        ceapply CongProjTwo
      | ceapply EqTyConv ; [ ceapply CongProjTwo | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (uniProd _ prop _ _) (uniProd _ prop _ _) _ =>
      first [
        ceapply CongUniProdProp
      | ceapply EqTyConv ; [ ceapply CongUniProdProp | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (uniProd _ _ _ _) (uniProd _ _ _ _) _ =>
      first [
        ceapply CongUniProd
      | ceapply EqTyConv ; [ ceapply CongUniProd | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (uniId _ _ _ _) (uniId _ _ _ _) _ =>
      first [
        ceapply CongUniId
      | ceapply EqTyConv ; [ ceapply CongUniId | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (uniBinaryProd prop prop _ _) (uniBinaryProd prop prop _ _) _ =>
      first [
        ceapply CongUniBinaryProdProp
      | ceapply EqTyConv ; [ ceapply CongUniBinaryProdProp | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G (uniBinaryProd _ _ _ _) (uniBinaryProd _ _ _ _) _ =>
      first [
        ceapply CongUniBinaryProd
      | ceapply EqTyConv ; [ ceapply CongUniBinaryProd | .. ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
    | |- eqterm ?G ?u ?v ?A =>
      tryif (is_var u ; is_var v)
      then first [
        eassumption
      | ceapply EqRefl
      | ceapply EqSym ; [ eassumption |.. ]
      | ceapply EqTyConv ; [ eassumption | .. ]
      | ceapply EqTyConv ; [
          ceapply EqSym ; [ eassumption | .. ]
        | ..
        ]
      | myfail debug
      ] ; magicn try shelf DoTysym debug
      else tryif (is_evar u + is_evar v)
        then tryif (do_shelf shelf)
          then shelve
          else myfail debug
        else myfail debug

    | _ => myfail debug
    end
  | do_try try
  ].

Ltac magic       := preop ; magicn DontTry DoShelf   DoTysym DoDebug.
Ltac okmagic     := preop ; magicn DontTry DoShelf   DoTysym DontDebug.
Ltac trymagic    := preop ; magicn DoTry   DoShelf   DoTysym DontDebug.
Ltac strictmagic := preop ; magicn DontTry DontShelf DoTysym DoDebug.

(* Tactic to keep judgments *)
Ltac keep_ju :=
  doConfig ;
  first [
    check_goal
  | shelve
  ].

(* Tactic to keep equalities *)
Ltac keep_eq :=
  doConfig ;
  lazymatch goal with
  | |- eqterm _ _ _ _ => idtac
  | |- eqtype _ _ _ => idtac
  | |- eqctx _ _ => idtac
  | _ => shelve
  end.

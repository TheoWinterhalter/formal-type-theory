(* In order to test our formalisation, we propose our own formalisation of a
   model that negates function extensionality, following Simon Boulier,
   Pierre-Marie Pédrot et Nicolas Tabareau.
*)

Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.

(* Source type theory *)
Module Stt.

  Section Stt.

  Local Instance hasPrecond : config.Precond
    := {| config.precondFlag := config.Yes |}.
  Context `{configReflection : config.Reflection}.
  Context `{ConfigSimpleProducts : config.SimpleProducts}.

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
  Context `{configReflection : config.Reflection}.
  Local Instance hasSimpleProducts : config.SimpleProducts
    := {| config.simpleproductsFlag := config.Yes |}.

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

Context `{configReflection : config.Reflection}.
Context `{configSimpleProducts : config.SimpleProducts}.

Axiom cheating : forall A : Type, A.
Ltac todo := apply cheating.

Fixpoint trans_ctx (G : context) : context :=
  match G with
  | ctxempty => ctxempty
  | ctxextend G A => ctxextend (trans_ctx G) (trans_type A)
  end

with trans_type (A : type) : type :=
  match A with
  | Prod A B => SimProd (Prod (trans_type A) (trans_type B)) Bool
  | Id A u v => Id (trans_type A) (trans_term u) (trans_term v)
  | Subst A sbs => Subst (trans_type A) (trans_subst sbs)
  | Empty => Empty
  | Unit => Unit
  | Bool => Bool
  | SimProd A B => SimProd (trans_type A) (trans_type B)
  end

with trans_term (t : term) : term :=
  match t with
  | var k => var k
  | lam A B u =>
    pair (Prod (trans_type A) (trans_type B))
         Bool
         (lam (trans_type A) (trans_type B) (trans_term u))
         true
  | app u A B v =>
    app (proj1 (Prod (trans_type A) (trans_type B)) Bool (trans_term u))
        (trans_type A)
        (trans_type B)
        (trans_term v)
  | refl A u => refl (trans_type A) (trans_term u)
  | j A u C w v p =>
    j (trans_type A)
      (trans_term u)
      (trans_type C)
      (trans_term w)
      (trans_term v)
      (trans_term p)
  | subst u sbs => subst (trans_term u) (trans_subst sbs)
  | exfalso A u => exfalso (trans_type A) (trans_term u)
  | unit => unit
  | true => true
  | false => false
  | cond C u v w =>
    cond (trans_type C) (trans_term u) (trans_term v) (trans_term w)
  | pair A B u v =>
    pair (trans_type A) (trans_type B) (trans_term u) (trans_term v)
  | proj1 A B p =>
    proj1 (trans_type A) (trans_type B) (trans_term p)
  | proj2 A B p =>
    proj2 (trans_type A) (trans_type B) (trans_term p)
  end

with trans_subst (sbs : substitution) : substitution :=
  match sbs with
  | sbzero A u => sbzero (trans_type A) (trans_term u)
  | sbweak A => sbweak (trans_type A)
  | sbshift A sbs => sbshift (trans_type A) (trans_subst sbs)
  | sbid => sbid
  | sbcomp sbs sbt => sbcomp (trans_subst sbs) (trans_subst sbt)
  end.

Ltac ih :=
  match goal with
  | trans_isctx :
      forall G,
        Stt.isctx G ->
        Ttt.isctx (trans_ctx G)
    |- isctx (trans_ctx ?G) =>
    now apply (trans_isctx G)
  | trans_istype :
      forall G A,
        Stt.istype G A ->
        Ttt.istype (trans_ctx G) (trans_type A)
    |- istype (trans_ctx ?G) (trans_type ?A) =>
    now apply (trans_istype G A)
  | trans_isterm :
      forall G u A,
        Stt.isterm G u A ->
        Ttt.isterm (trans_ctx G) (trans_term u) (trans_type A)
    |- isterm (trans_ctx ?G) (trans_term ?u) (trans_type ?A) =>
    now apply (trans_isterm G u A)
  | trans_issubst :
      forall sbs G D,
        Stt.issubst sbs G D ->
        Ttt.issubst (trans_subst sbs) (trans_ctx G) (trans_ctx D)
    |- issubst (trans_subst ?sbs) (trans_ctx ?G) (trans_ctx ?D) =>
    now apply (trans_issubst sbs G D)
  | trans_eqctx :
      forall G D,
        Stt.eqctx G D ->
        Ttt.eqctx (trans_ctx G) (trans_ctx D)
    |- eqctx (trans_ctx ?G) (trans_ctx ?D) =>
    now apply (trans_eqctx G D)
  | trans_eqtype :
      forall G A B,
        Stt.eqtype G A B ->
        Ttt.eqtype (trans_ctx G) (trans_type A) (trans_type B)
    |- eqtype (trans_ctx ?G) (trans_type ?A) (trans_type ?B) =>
    now apply (trans_eqtype G A B)
  | trans_eqterm :
      forall G u v A,
        Stt.eqterm G u v A ->
        Ttt.eqterm (trans_ctx G) (trans_term u) (trans_term v) (trans_type A)
    |- eqterm (trans_ctx ?G) (trans_term ?u) (trans_term ?v) (trans_type ?A) =>
    now apply (trans_eqterm G u v A)
  | trans_eqsubst :
      forall sbs sbt G D,
        Stt.eqsubst sbs sbt G D ->
        Ttt.eqsubst (trans_subst sbs)
                    (trans_subst sbt)
                    (trans_ctx G)
                    (trans_ctx D)
    |- eqsubst (trans_subst ?sbs)
              (trans_subst ?sbt)
              (trans_ctx ?G)
              (trans_ctx ?D) =>
    now apply (trans_eqsubst sbs sbt G D)
  end.

Fixpoint trans_isctx {G} (H : Stt.isctx G) {struct H} :
  Ttt.isctx (trans_ctx G)

with trans_istype {G A} (H : Stt.istype G A) {struct H} :
  Ttt.istype (trans_ctx G) (trans_type A)

with trans_isterm {G u A} (H : Stt.isterm G u A) {struct H} :
  Ttt.isterm (trans_ctx G) (trans_term u) (trans_type A)

with trans_issubst {sbs G D} (H : Stt.issubst sbs G D) {struct H} :
  Ttt.issubst (trans_subst sbs) (trans_ctx G) (trans_ctx D)

with trans_eqctx {G D} (H : Stt.eqctx G D) {struct H} :
  Ttt.eqctx (trans_ctx G) (trans_ctx D)

with trans_eqtype {G A B} (H : Stt.eqtype G A B) {struct H} :
  Ttt.eqtype (trans_ctx G) (trans_type A) (trans_type B)

with trans_eqterm {G u v A} (H : Stt.eqterm G u v A) {struct H} :
  Ttt.eqterm (trans_ctx G) (trans_term u) (trans_term v) (trans_type A)

with trans_eqsubst {sbs sbt G D} (H : Stt.eqsubst sbs sbt G D) {struct H} :
  Ttt.eqsubst (trans_subst sbs) (trans_subst sbt) (trans_ctx G) (trans_ctx D).

Proof.

  (* trans_isctx *)
  - { destruct H ; doConfig.

      (* CtxEmpty *)
      - constructor.

      (* CtxExtend *)
      - simpl. config constructor.
        ih.
    }

  (* trans_istype *)
  - { destruct H ; doConfig.

      (* TyCtxConv *)
      - { (config apply @TyCtxConv with (G := trans_ctx G)) ; ih. }

      (* TySubst *)
      - { simpl.
          config apply @TySubst with (D := trans_ctx D).
          - ih.
          - ih.
        }

      (* TyProd *)
      - { simpl.
          capply TySimProd.
          - todo. (* Where is the hypothesis that Ttt has simple products? *)
          - capply TyProd.
            now apply (trans_istype (ctxextend G A) B).
          (* Too bad ih doesn't deal with this*)
          - capply TyBool. ih.
        }

      (* TyId *)
      - { simpl. capply TyId.
          - ih.
          - ih.
        }

      (* TyEmpty *)
      - capply TyEmpty ; ih.

      (* TyUnit *)
      - capply TyUnit ; ih.

      (* TyBool *)
      - capply TyBool ; ih.

      (* TySimProd *)
      - { simpl. capply TySimProd.
          - todo. (* I'm not good with type classes yet *)
          - ih.
          - ih.
        }
    }

  (* trans_isterm *)
  - { destruct H ; doConfig.

      (* TermTyConv *)
      - { config apply @TermTyConv with (A := trans_type A).
          - ih.
          - ih.
        }

      (* TermCtxConv *)
      - { config apply @TermCtxConv with (G := trans_ctx G).
          - ih.
          - ih.
        }

      (* TermSubst *)
      - { simpl.
          config apply @TermSubst with (D := trans_ctx D).
          - ih.
          - ih.
        }

      (* TermVarZero *)
      - { simpl. capply TermVarZero. ih. }

      (* TermVarSucc *)
      - { simpl. capply TermVarSucc.
          - now apply (trans_isterm G (var k) A).
          - ih.
        }

      (* TermAbs *)
      - { simpl.
          capply TermPair.
          - todo.(* type classes problem *)
          - capply TermAbs.
            now apply (trans_isterm (ctxextend G A) u B).
          - capply TermTrue. ih.
        }

      (* TermApp *)
      - { simpl.
          capply TermApp.
          - capply TermProj1.
            + todo. (* type classes *)
            + now apply (trans_isterm G u (Prod A B)).
          - ih.
        }

      (* TermRefl *)
      - { simpl. capply TermRefl. ih. }

      (* TermJ *)
      - { simpl. capply TermJ.
          - ih.
          - now apply (trans_istype (ctxextend (ctxextend G A)
            (Id (Subst A (sbweak A)) (subst u (sbweak A)) (var 0))) C).
          - now apply (trans_isterm G w
         (Subst
            (Subst C
               (sbshift (Id (Subst A (sbweak A)) (subst u (sbweak A)) (var 0))
                  (sbzero A u))) (sbzero (Id A u u) (refl A u)))).
          - ih.
          - now apply (trans_isterm G p (Id A u v)).
        }

      (* TermExfalso *)
      - { simpl. capply TermExfalso.
          - ih.
          - now apply (trans_isterm G u Empty).
        }

      (* TermUnit *)
      - { simpl. capply TermUnit. ih. }

      (* TermTrue *)
      - { simpl. capply TermTrue. ih. }

      (* TermFalse *)
      - { simpl. capply TermFalse. ih. }

      (* TermCond *)
      - { simpl. capply TermCond.
          - now apply (trans_isterm G u Bool).
          - now apply (trans_istype (ctxextend G Bool) C).
          - now apply (trans_isterm G v (Subst C (sbzero Bool true))).
          - now apply (trans_isterm G w (Subst C (sbzero Bool false))).
        }

      (* TermPair *)
      - { simpl. capply TermPair.
          - todo. (* type classes *)
          - ih.
          - ih.
        }

      (* TermProj1 *)
      - { simpl. capply TermProj1.
          - todo. (* type classes *)
          - now apply (trans_isterm G p (SimProd A B)).
        }

      (* TermProj2 *)
      - { simpl. capply TermProj2.
          - todo. (* type classes *)
          - now apply (trans_isterm G p (SimProd A B)).
        }
    }

  (* trans_issubst *)
  - todo.

  (* trans_eqctx *)
  - todo.

  (* trans_eqtype *)
  - todo.

  (* trans_eqterm *)
  - todo.

  (* trans_eqsubst *)
  - todo.
Qed.

End Translation.

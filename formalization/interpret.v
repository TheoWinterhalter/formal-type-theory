Require config.
Require Import config_tactics.

Local Open Scope type_scope.

Require Import syntax. (* The syntax of ett/ptt. *)
Require Import tt.

Require ptt ett ett_sanity.
Require pxtt.

Axiom cheating : forall (A : Type), A.
Ltac todo := apply cheating.

Definition transport {A} {u v} (P : A -> Type) (p : u = v) : P u -> P v :=
  match p in (_ = u') return P u -> P u'
  with
  | eq_refl => fun x => x
  end.

Definition Family (G : Set) := G -> Set.

Definition section {G : Set} (A : Family G) :=
  forall x, A x.

Definition Pi {G} (A : Family G) (B : Family (sigT A)) :=
  fun xs => forall (x : A xs), B (existT _ xs x).

Inductive istran_ctx : context -> Set -> Type :=
  | istran_ctx_ctxempty : istran_ctx ctxempty Datatypes.unit
  | istran_ctx_ctxextend :
      forall G G' A A',
        istran_ctx G G' ->
        istran_type G G' A A' ->
        istran_ctx (ctxextend G A) (sigT A')

with istran_type :
  (forall (G : context) (G' : Set) (A : type) (A' : Family G'), Type) :=
 | istran_type_Empty :
     forall G G', istran_type G G' Empty (fun _ => Empty_set)
 | istran_type_Unit :
     forall G G', istran_type G G' Unit (fun _ => Datatypes.unit)
 | istran_type_Prod :
     forall G G' A A' B B',
       istran_type G G' A A' ->
       istran_type (ctxextend G A) (sigT A') B B' ->
       istran_type G G' (Prod A B) (Pi A' B')

 | istran_type_todo :
     forall (G : context) (G' : Set) (A : type) (A' : Family G'),
       istran_type G G' A A'.

Fixpoint eval_ctx G (Der : pxtt.isctx G) {struct Der} :
  { G' : Set & istran_ctx G G' }

with eval_subst {G D G' sbs} (Der : pxtt.issubst sbs G D) {struct Der} :
   istran_ctx G G' ->
   { D' : Set
   & istran_ctx D D'
   * (Family D' -> Family G') }

with eval_ty {G G' A} (Der : pxtt.istype G A) {struct Der} :
  istran_ctx G G' ->
  { A' : Family G' & istran_type G G' A A' }

with eval_term {G G' A A' u} (Der : pxtt.isterm G u A) {struct Der} :
  istran_ctx G G' ->
  istran_type G G' A A' ->
  section A'

with eval_eqctx_lr {G G' D} (Der : pxtt.eqctx G D) {struct Der} :
  istran_ctx G G' ->
  { D' : Set & istran_ctx D D' * (D' = G') }

with eval_eqctx_rl {G D D'} (Der : pxtt.eqctx G D) {struct Der} :
  istran_ctx D D' ->
  { G' : Set & istran_ctx G G' * (G' = D') }

with eval_eqtype_lr {G G' A A' B} (Der : pxtt.eqtype G A B) {struct Der} :
  istran_ctx G G' ->
  istran_type G G' A A' ->
  { B' : Family G' & istran_type G G' B B' * (A' = B') }

with eval_eqtype_rl {G G' A B B'} (Der : pxtt.eqtype G A B) {struct Der} :
  istran_ctx G G' ->
  istran_type G G' B B' ->
  { A' : Family G' & istran_type G G' A A' * (A' = B') }.


Proof.
  (* eval_ctx *)
  - { destruct Der ; doConfig.

      (* CtxEmpty *)
      - exists Datatypes.unit.
        constructor.

      (* CtxExtend *)
      - { destruct (eval_ctx G i) as [G' ist_GG'].
          destruct (eval_ty G G' A i0 ist_GG') as [A' ist_AA'].
          exists (sigT A').
          now constructor.
        }
    }

  (* eval_subst *)
  - { destruct Der ; doConfig.

      (* SubstZero *)
      - { intro ist_GG'.
          destruct (eval_ty G G' A i0 ist_GG') as [A' ist_AA'].
          pose (u' := eval_term G G' A A' u i ist_GG' ist_AA').
          exists (sigT A').
          split.
          - now constructor.
          - intros B' xs.
            exact (B' (existT _ xs (u' xs))).
        }

      (* SubstWeak *)
      - { rename G' into G'A'.
          intro ist_G'A'.
          inversion ist_G'A'. subst.
          exists G'. split.
          - assumption.
          - intros B' [xs x].
            exact (B' xs).
        }

      (* SubstShift *)
      - { rename G' into GAs'.
          intro ist_GAs'.
          inversion ist_GAs'. subst. rename A' into As'.
          rename X into ist_G'. rename X0 into ist_As'.
          (* inversion ist_As'. We have to wait until it makes sense. *)
          todo.
        }

      (* SubstId *)
      - { intro ist_GG'.
          exists G'. split.
          - assumption.
          - exact (fun x => x).
        }

      (* SubstComp *)
      - { intro ist_GG'.
          destruct (eval_subst G D G' sbs Der1 ist_GG') as [D' [ist_DD' sbs']].
          destruct (eval_subst D E D' sbt Der2 ist_DD') as [E' [ist_EE' sbt']].
          exists E'. split.
          - assumption.
          - intro C. apply sbs'. apply sbt'. exact C.
        }

      (* SubstCtxConv *)
      - { rename G' into G2'.
          intro ist_G2'.
          destruct (eval_eqctx_rl G1 G2 G2' e ist_G2') as [G1' [ist_G1' eqG]].
          destruct (eval_subst G1 D1 G1' sbs Der ist_G1') as [D1' [ist_D1' sbs']].
          destruct (eval_eqctx_lr D1 D1' D2 e0 ist_D1') as [D2' [ist_D2' eqD]].
          exists D2'. split.
          - assumption.
          - rewrite eqD.
            rewrite <- eqG. exact sbs'.
        }
  }

  (* eval_ty *)
  - { destruct Der ; doConfig.

      (* TyCtxConv *)
      - { intros ist_DG'.
          rename G' into D'.
          destruct (eval_eqctx_rl G D D' e ist_DG') as [G' [ist_GG' eq_G'D']].
          destruct eq_G'D'.
          destruct (eval_ty G G' A Der ist_GG') as [A' ist_AA'].
          exists A'.
          constructor.
        }

      (* TySubst *)
      - { intros ist_GG'.
          destruct (eval_subst G D G' sbs i ist_GG') as [D' [ist_DD' sbs']].
          destruct (eval_ty D D' A Der ist_DD') as [A' ist_AA'].
          pose (A'' := sbs' A').
          exists A''.
          constructor.
        }

      (* TyProd *)
      - { intros ist_GG'.
          destruct (eval_ty G G' A i ist_GG') as [A' ist_AA'].
          pose (G'A' := sigT A').
          destruct (eval_ty (ctxextend G A) G'A' B Der) as [B' ist_BB'].
          { now constructor. }
          exists (Pi A' B').
          now constructor.
        }

      (* TyId *)
      - { intros ist_GG'.
          destruct (eval_ty G G' A i0 ist_GG') as [A' ist_AA'].
          pose (u' := eval_term G G' A A' u i1 ist_GG' ist_AA').
          pose (v' := eval_term G G' A A' v i2 ist_GG' ist_AA').
          exists (fun xs => u' xs = v' xs).
          now constructor.
        }

      (* TyEmpty *)
      - { intros _.
          exists (fun _ => Datatypes.Empty_set).
          now constructor.
        }

      (* TyUnit *)
      - { intros _.
          exists (fun _ => Datatypes.unit).
          now constructor.
        }

      (* TyBool *)
      - { intros _.
          exists (fun _ => Datatypes.bool).
          now constructor.
        }
    }

    (* eval_term *)
  - { destruct Der ; doConfig.

      (* TermTyConv *)
      - { rename A' into B'.
          intros istG' istB'.
          destruct (eval_eqtype_rl G G' A B B' e istG' istB') as [A' [istA' eq]].
          pose (u' := eval_term G G' A A' u Der istG' istA').
          rewrite <- eq.
          exact u'.
        }

      (* TermCtxConv *)
      - { rename G' into D'.
          intros istD' istA'.
          destruct (eval_eqctx_rl G D D' e istD') as [G' [istG' eq]].
          pose (eq' := eq_sym eq).
          pose (A'' := transport Family eq' A').
          assert (istA'' : istran_type G G' A A'').
          { constructor. }
          pose (u' := eval_term G G' A A'' u Der istG' istA'').
          intro xs.
          pose (ys := transport _ eq' xs). simpl in ys.
          pose (uy := u' ys).
          (* I need to say that A' is equal to A'' somehow don't I? *)
          todo.
        }

      (* TermSubst *)
      - { rename A' into As'.
          intros istG' istAs'.
          (* Not enough to go on... *)
          (* inversion istAs'. subst. *)

          (* destruct (eval_subst G D G' sbs i istG') as [D' [istD' sbs']]. *)
          (* pose (u' := eval_term D D' A A' Der istD' istA'). *)
          todo.
        }

      (* TermVarZero *)
      - { rename G' into GA', A' into Aw'.
          intros istGA' istAw'.
          inversion istGA'. subst.
          rename X into istG', X0 into istA'.
          (* Now we need to invert istAw', but that isn't possible at the
             moment *)
          todo.
        }

      (* TermVarSucc *)
      - todo.

      (* TermAbs *)
      - todo.

      (* TermApp *)
      - todo.

      (* TermRefl *)
      - todo.

      (* TermJ *)
      - todo.

      (* TermExfalso *)
      - todo.

      (* TermUnit *)
      - todo.

      (* TermTrue *)
      - todo.

      (* TermFalse *)
      - todo.

      (* TermCond *)
      - todo.
    }

  (* eval_eqctx_lr *)
  - { destruct Der ; doConfig.

      (* CtxRefl *)
      - { intro istG'.
          exists G'. split.
          - assumption.
          - reflexivity.
        }

      (* CtxSym *)
      - { rename G' into D'. intro istD'.
          destruct (eval_eqctx_rl G D D' Der istD') as [G' [istG' eq]].
          exists G'. split.
          - assumption.
          - assumption.
        }

      (* CtxTrans *)
      - { intro istG'.
          destruct (eval_eqctx_lr G G' D Der1 istG') as [D' [istD' eq1]].
          destruct (eval_eqctx_lr D D' E Der2 istD') as [E' [istE' eq2]].
          exists E'. split.
          - assumption.
          - now transitivity D'.
        }

      (* EqCtxEmpty *)
      - { intro istG'.
          inversion istG'. subst.
          now exists (Datatypes.unit).
        }

      (* EqCtxExtend *)
      - { rename G' into G'A'.
          intro istG'A'.
          inversion istG'A'. subst.
          rename X into istG', X0 into istA'.
          destruct (eval_eqtype_lr G G' A A' B e istG' istA') as [B' [istB' eqA]].
          destruct (eval_eqctx_lr G G' D Der istG') as [D' [istD' eqG]].
          assert (eq' : G' = D').
          { now destruct eqG. }
          pose (B'' := transport Family eq' B').
          assert (istB'' : istran_type D D' B B'').
          { (* This holds because the relation is trivial only!!! *)
            constructor.
          }
          exists (sigT B''). split.
          - now constructor.
          - refine (
              match eqG as p in (_ = E')
              return forall (A'' : Family E') (q : transport Family p B'' = A''), { x : D' & B'' x } = { x : E' & A'' x }
              with eq_refl => _
              end _ _
            ).
            + intros A'' eq.
              simpl in eq.
              now rewrite eq.
            + (* eq' should be the symmetry of eqG and thus application of
                 transport twice should be the identity. *)
              todo.
        }
    }

  (* eval_eqctx_rl *)
  - { destruct Der ; doConfig.

      (* CtxRefl *)
      - { rename D' into G'.
          intro istG'.
          exists G'. split.
          - assumption.
          - reflexivity.
        }

      (* CtxSym *)
      - { rename D' into G'. intro istG'.
          destruct (eval_eqctx_lr G G' D Der istG') as [D' [istD' eq]].
          exists D'. split.
          - assumption.
          - assumption.
        }

      (* CtxTrans *)
      - { rename D' into E'.
          intro istE'.
          destruct (eval_eqctx_rl D E E' Der2 istE') as [D' [istD' eq2]].
          destruct (eval_eqctx_rl G D D' Der1 istD') as [G' [istG' eq1]].
          exists G'. split.
          - assumption.
          - now transitivity D'.
        }

      (* EqCtxEmpty *)
      - { intro istG'.
          inversion istG'. subst.
          now exists (Datatypes.unit).
        }

      (* EqCtxExtend *)
      - { rename D' into D'B'.
          intro istD'B'.
          inversion istD'B'. subst.
          rename G' into D', A' into B'.
          (* We need to know how to destruct a type equality first! *)
          todo.
        }
    }

  (* eval_eqtype_lr *)
  - todo.

  (* eval_eqtype_rl *)
  - todo.
Defined.

Lemma empty_to_empty :
  let Der := (TyEmpty CtxEmpty : pxtt.istype ctxempty Empty) in
  let ist_GG' := istran_ctx_ctxempty : istran_ctx ctxempty Datatypes.unit in
  forall xs, projT1 (eval_ty Der ist_GG') xs = Empty_set.
Proof.
  reflexivity.
Qed.

Lemma consistency : forall u, pxtt.isterm ctxempty u Empty -> Empty_set.
Proof.
  intros u Der.
  pose (ist_GG' := istran_ctx_ctxempty : istran_ctx ctxempty Datatypes.unit).
  pose (tr := eval_ty (TyEmpty CtxEmpty) ist_GG').
  pose (u' := eval_term Der ist_GG' (projT2 tr)).
  pose (p := u' tt). apply p.
Qed.

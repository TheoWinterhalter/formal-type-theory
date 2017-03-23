Require Import Coq.Program.Equality.

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

Definition Family (G : Set) : Type := G -> Set.

Definition section {G : Set} (A : Family G) :=
  forall x, A x.

Definition Pi {G} (A : Family G) (B : Family (sigT A)) :=
  fun xs => forall (x : A xs), B (existT _ xs x).

Definition Eq {G} (A : Family G) (u v : section A) :=
  fun xs => u xs = v xs.

Axiom funext :
  forall (A : Set) (B : A -> Type) (f g : forall x, B x),
    (forall x, f x = g x) -> f = g.

Definition UIP (T : Type) :=
  forall {x : T} (p : x = x), (p = eq_refl x).

Axiom UIP_Set : UIP Set.

Arguments UIP_Set {_} _.

Lemma UIP_exp (X Y : Type) : UIP Y -> UIP (X -> Y).
Proof.
  todo.
Defined.

Definition UIP_Family (A : Set) := UIP_exp A Set (@UIP_Set).

Arguments UIP_Family {_} {_} _.


Inductive istran_ctx : context -> Set -> Type :=

  | istran_ctxempty :
      istran_ctx ctxempty Datatypes.unit

  | istran_ctxextend :
      forall G G' A A',
        istran_ctx G G' ->
        istran_type G G' A A' ->
        istran_ctx (ctxextend G A) (sigT A')

with istran_subst :
  forall (G : context) (G' : Set)
    (D : context) (D' : Set)
    (sbs : substitution) (sbs' : G' -> D'),
    Type
  :=

  | istran_subst_sbzero :
      forall G G' A A' u u',
        istran_ctx G G' ->
        istran_type G G' A A' ->
        istran_term G G' A A' u u' ->
        istran_subst G G' (ctxextend G A) (sigT A') (sbzero A u)
                     (fun xs => existT _ xs (u' xs))

  | istran_subst_sbweak :
      forall G G' A A',
        istran_ctx G G' ->
        istran_type G G' A A' ->
        istran_subst (ctxextend G A) (sigT A') G G' (sbweak A)
                     (@projT1 _ _)

  | istran_subst_sbshift :
      forall G G' D D' A A' sbs sbs',
        istran_ctx G G' ->
        istran_ctx D D' ->
        istran_type D D' A A' ->
        istran_subst G G' D D' sbs sbs' ->
        istran_subst
          (ctxextend G (Subst A sbs)) (sigT (fun xs => A' (sbs' xs)))
          (ctxextend D A) (sigT A')
          (sbshift A sbs) (fun xs => existT _ (sbs' (projT1 xs)) (projT2 xs))

  | istran_subst_sbid :
      forall G G',
        istran_ctx G G' ->
        istran_subst G G' G G' sbid (fun x => x)

  | istran_subst_sbcomp :
      forall G G' D D' E E' sbs sbs' sbt sbt',
        istran_ctx G G' ->
        istran_ctx D D' ->
        istran_ctx E E' ->
        istran_subst G G' D D' sbs sbs' ->
        istran_subst D D' E E' sbt sbt' ->
        istran_subst G G' E E'
                     (sbcomp sbt sbs) (fun xs => sbt' (sbs' xs))

with istran_type' :
  (forall (G : context) (G' : Set) (A : type) (A' : Family G'), Type) :=

 | istran_Prod :
     forall G G' A A' B B',
       istran_type G G' A A' ->
       istran_type (ctxextend G A) (sigT A') B B' ->
       istran_type' G G' (Prod A B) (Pi A' B')

 | istran_Id :
     forall G G' A A' u u' v v',
       istran_type G G' A A' ->
       istran_term G G' A A' u u' ->
       istran_term G G' A A' v v' ->
       istran_type' G G' (Id A u v) (Eq A' u' v')

 | istran_Subst :
     forall G G' D D' A A' sbs sbs',
       istran_type D D' A A' ->
       istran_subst G G' D D' sbs sbs' ->
       istran_type' G G' (Subst A sbs) (fun xs => A' (sbs' xs))

 | istran_Empty :
     forall G G',
       istran_ctx G G' ->
       istran_type' G G' Empty (fun _ => Empty_set)

 | istran_Unit :
     forall G G',
       istran_ctx G G' ->
       istran_type' G G' Unit (fun _ => Datatypes.unit)

 | istran_Bool :
     forall G G',
       istran_ctx G G' ->
       istran_type' G G' Bool (fun _ => Datatypes.bool)

with istran_type :
       (forall (G : context) (G' : Set) (A : type) (A' : Family G'), Type) :=

 | istran_TyCtxConv :
     forall G G' D D' A A' p,
       istran_type' G G' A A' ->
       istran_eqctx G G' D D' p ->
       istran_type D D' A (transport Family p A')

with istran_term :
  forall (G : context) (G' : Set)
    (A : type) (A' : Family G')
    (u : term) (u' : section A'),
    Type
  :=

  | istran_refl :
      forall G G' A A' u u',
        istran_term G G' A A' u u' ->
        istran_term G G' (Id A u u) (Eq A' u' u') (refl A u) (fun xs => eq_refl (u' xs))

  | istran_todo :
      forall G G' A A' u u', istran_term G G' A A' u u'

with istran_eqctx :
  forall (G : context) (G' : Set)
         (D : context) (D' : Set),
    G' = D' -> Type :=
  | istran_eqctx_todo :
      forall G G' D D' p, istran_eqctx G G' D D' p.

Lemma ap_path {X Y} (f : X -> Y) {x y} : x = y -> f x = f y.
Proof.
  intro p ; destruct p; reflexivity.
Defined.

Lemma path_sigT :
  forall u v : { X : Set & X -> Set },
    u = v ->
    sigT (projT2 u) = sigT (projT2 v).
Proof.
  intros u v p.
  destruct p.
  reflexivity.
Defined.

Lemma path_existT {A : Type} {B : A -> Type} {u v : sigT B} :
  forall (p : projT1 u = projT1 v),
    transport _ p (projT2 u) = projT2 v -> u = v.
Proof.
  intros p q.
  destruct u as [x x'].
  destruct v as [y y'].
  simpl in p.
  destruct p.
  simpl in q.
  destruct q.
  reflexivity.
Defined.

Lemma path_projT2 {A : Type} {B : A -> Type} {u v : sigT B} (p : u = v) :
  transport B (ap_path (@projT1 _ _) p) (projT2 u) = projT2 v.
Proof.
  destruct p ; reflexivity.
Defined.

Lemma path_decompose_existT {A : Type} {B : A -> Type} {x y : A}
      {u : B x} {v : B y} :
  forall (r : existT _ x u = existT _ y v),
    { p : x = y & transport _ p u = v }.
Proof.
  intros r.
  exists (ap_path (@projT1 _ _) r).
  exact (path_projT2 r).
Defined.

Fixpoint cohere_ctx G G' G''
  (H1 : istran_ctx G G')
  (H2 : istran_ctx G G'') {struct H1} :
  G' = G''

with cohere_subst G G' G'' D D' D'' sbs sbs' sbs''
  (H1 : istran_subst G G'  D D'  sbs sbs')
  (H2 : istran_subst G G'' D D'' sbs sbs'') {struct H1} :
  existT _ G' (existT _ D' sbs') = existT _ G'' (existT _ D'' sbs'')
    :> { X : Set & { Y : Set & X -> Y } }

with cohere_type' G G' G'' A A' A''
  (H1 : istran_type' G G'  A A')
  (H2 : istran_type' G G'' A A'') {struct H1} :
  existT _ G' A' = existT _ G'' A'' :> sigT Family

with cohere_type G G' G'' A A' A''
  (H1 : istran_type G G'  A A')
  (H2 : istran_type G G'' A A'') {struct H1} :
  existT _ G' A' = existT _ G'' A'' :> sigT Family

with cohere_term G G' G'' A A' A'' u u' u''
  (H1 : istran_term G G'  A A'  u u')
  (H2 : istran_term G G'' A A'' u u'') {struct H1} :
  existT _ G' (existT _ A' u') = existT _ G'' (existT _ A'' u'')
    :> { X : Set & { F : Family X & section F } }
.

Proof.
  (* cohere_ctx *)
  - { destruct G ; doConfig ;
      dependent destruction H1 ;
      dependent destruction H2.

      (* ctxempty *)
      - { reflexivity. }

      (* ctxextend *)
      - {
          rename
            t into A,
            G'0 into G'',
            A'0 into A''.
            apply (path_sigT (existT _ G' A') (existT _ G'' A'')).
            now apply (cohere_type G G' G'' A A' A'').
        }
    }

  (* cohere_subst *)
  - { todo. }

  (* cohere_type' *)
  - { destruct H1 ; dependent destruction H2.

      (* Prod *)
      - {
          rename
            G'0 into G'', A'0 into A'', B'0 into B''.
          pose (p := cohere_type _ _ _ _ _ _ i i1).
          pose (r := path_projT2 p).
          pose (q := ap_path (@projT1 _ _) p) ; simpl in q.
          replace (ap_path (@projT1 _ _) p) with q in r by reflexivity.
          pose (s := cohere_type _ _ _ _ _ _ i0 i2).
          apply @path_existT with (p := q).
          destruct q.
          simpl in r.
          destruct r.
          simpl.
          pose (t := path_projT2 s).
          rewrite (UIP_Set (ap_path (@projT1 _ _) s)) in t.
          simpl in t.
          destruct t.
          reflexivity.
        }

      (* Id *)
      - {
          rename
            G'0 into G'', A'0 into A'', u'0 into u'', v'0 into v''.
          pose (p := cohere_term _ _ _ _ _ _ _ _ _ i0 i3).
          destruct (path_decompose_existT p) as [q r].
          destruct q ; simpl in r.
          destruct (path_decompose_existT r) as [qq rr].
          destruct qq ; simpl in rr.
          destruct rr.
          pose (p' := cohere_term _ _ _ _ _ _ _ _ _ i1 i4).
          destruct (path_decompose_existT p') as [q' r'].
          rewrite (UIP_Set q') in r'.
          simpl in r'.
          destruct (path_decompose_existT r') as [qq' rr'].
          rewrite (UIP_Family qq') in rr' ; simpl in rr'.
          destruct rr'.
          reflexivity.
        }

      (* Subst *)
      - {
          todo.
        }

      (* Empty *)
      - {
          destruct (cohere_ctx _ _ _ i i0).
          reflexivity.
        }

      (* Unit *)
      - {
          destruct (cohere_ctx _ _ _ i i0).
          reflexivity.
        }

      (* Bool *)
      - {
          destruct (cohere_ctx _ _ _ i i0).
          reflexivity.
        }
    }

    (* cohere_type *)
    - { todo.
    }

    (* cohere_term *)
    - {
        todo.
      }
Defined.

Print Assumptions cohere_ctx.

Fixpoint eval_ctx G (Der : pxtt.isctx G) {struct Der} :
  { G' : Set & istran_ctx G G' }

with eval_subst {G D sbs} (Der : pxtt.issubst sbs G D) {struct Der} :
  { G' : Set &
    istran_ctx G G' * {
    D' : Set &
    istran_ctx D D' * {
    sbs' : G' -> D' &
    istran_subst G G' D D' sbs sbs'
  } } }

with eval_type {G A} (Der : pxtt.istype G A) {struct Der} :
  { G' : Set &
    istran_ctx G G' * {
    A' : Family G' &
    istran_type G G' A A'
  } }

with eval_term {G A u} (Der : pxtt.isterm G u A) {struct Der} :
  { G' : Set &
    istran_ctx G G' * {
    A' : Family G' &
    istran_type G G' A A' * {
    u' : section A' &
    istran_term G G' A A' u u'
  } } }

with eval_eqctx {G D} (Der : pxtt.eqctx G D) {struct Der} :
  { G' : Set &
    istran_ctx G G' * {
    D' : Set &
    istran_ctx D D' *
    G' = D'
  } }

with eval_eqtype {G A B} (Der : pxtt.eqtype G A B) {struct Der} :
  { G' : Set &
    istran_ctx G G' * {
    A' : Family G' &
    istran_type G G' A A' * {
    B' : Family G' &
    istran_type G G' B B' *
    (A' = B')
  } } }.

Proof.
  (* eval_ctx *)
  - { destruct Der ; doConfig.

      (* CtxEmpty *)
      - exists Datatypes.unit.
        constructor.

      (* CtxExtend *)
      - { destruct (eval_type _ _ i0) as [G' [ist_GG' [A' ist_A']]].
          exists (sigT A').
          now constructor.
        }
    }

  (* eval_subst *)
  - { destruct Der ; doConfig.

      (* SubstZero *)
      - { destruct (eval_term _ _ _ i) as
              (G' & ist_G' & A' & ist_A' & u' & ist_u').
          exists G'.
          split ; [ assumption | ..].
          exists (sigT A').
          split ; [ now constructor | ..].
          eexists.
          econstructor ; eassumption.
        }

      (* SubstWeak *)
      - { destruct (eval_type _ _ i) as (G' & ist_G' & A' & ist_A').
          exists (sigT A').
          split ; [ now constructor | ..].
          exists G'.
          split ; [ assumption | ..].
          eexists.
          econstructor ; eassumption.
        }

      (* SubstShift *)
      - { destruct (eval_subst _ _ _ Der) as
              (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs').
          destruct (eval_type _ _ i) as (D'' & ist_D'' & A' & ist_A').
          destruct (cohere_ctx _ _ _ ist_D' ist_D'').
          exists (sigT (fun xs => A' (sbs' xs))).
          split.
          - constructor.
            + assumption.
            + apply (istran_TyCtxConv G G' G G' _ _ (eq_refl)).
              * econstructor ; eassumption.
              * constructor.
          - exists (sigT A').
            split ; [ now constructor | ..].
            eexists.
            econstructor ; eassumption.
        }

      (* SubstId *)
      - { intro ist_GG'.
          exists G'. split.
          - assumption.
          - todo.
        }

      (* SubstComp *)
      - { intro ist_GG'.
          destruct (eval_subst G D G' sbs Der1 ist_GG') as [D' [ist_DD' sbs']].
          destruct (eval_subst D E D' sbt Der2 ist_DD') as [E' [ist_EE' sbt']].
          exists E'. split.
          - assumption.
          - todo.
        }

      (* SubstCtxConv *)
      - { todo.
          (* rename G' into G2'. *)
          (* intro ist_G2'. *)
          (* destruct (eval_eqctx_rl G1 G2 G2' e ist_G2') as [G1' [ist_G1' eqG]]. *)
          (* destruct (eval_subst G1 D1 G1' sbs Der ist_G1') as [D1' [ist_D1' sbs']]. *)
          (* destruct (eval_eqctx_lr D1 D1' D2 e0 ist_D1') as [D2' [ist_D2' eqD]]. *)
          (* exists D2'. split. *)
          (* - assumption. *)
          (* - rewrite eqD. *)
          (*   rewrite <- eqG. exact sbs'. *)
        }
  }

  (* eval_ty *)
  - { destruct Der ; doConfig.

      (* TyCtxConv *)
      - { rename G' into D'.
          intros ist_DD'.
          destruct (eval_eqctx_rl G D D' e ist_DD') as [G' [ist_GG' eq_G'D']].
          destruct (eval_type G G' A Der ist_GG') as [A' ist_AA'].
          pose (A'' := transport Family eq_G'D' A').
          exists A''.
          destruct eq_G'D'.
          simpl in A''.
          subst A''.

          todo.
        }

      (* TySubst *)
      - { intros ist_GG'.
          destruct (eval_subst G D G' sbs i ist_GG') as [D' [ist_DD' sbs']].
          destruct (eval_ty D D' A Der ist_DD') as [A' ist_AA'].
          pose (A'' := sbs' A').
          exists A''.
          econstructor.
          - eassumption.
          - todo. (* Translation of substitution should produce certificate. *)
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
          exists (Eq A' u' v').
          constructor.
          - assumption.
          - todo. (* Missing certificate *)
          - todo.
        }

      (* TyEmpty *)
      - { intros istG'.
          exists (fun _ => Datatypes.Empty_set).
          now constructor.
        }

      (* TyUnit *)
      - { intros istG'.
          exists (fun _ => Datatypes.unit).
          now constructor.
        }

      (* TyBool *)
      - { intros istG'.
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
          { todo. (* Coherence! *) }
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
          { (* Coherence problem *)
            todo.
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
  - { destruct Der ; doConfig.

      (* EqTyCtxConv *)
      - { rename G' into D'.
          intros istD' istA'.
          destruct (eval_eqctx_rl G D D' e istD') as [G' [istG' eq]].
          pose (A'' := transport Family (eq_sym eq) A').
          assert (istA'' : istran_type G G' A A'').
          { todo. (* Coherence *) }
          destruct (eval_eqtype_lr G G' A A'' B Der istG' istA'')
            as [B' [istB' eq']].
          pose (B'' := transport _ eq B').
          exists B''. split.
          - todo. (* Coherence again *)
          - todo. (* Coherence of another kind? *)
            (* When you think about it, all these coherence issues that arise
               and that might be solved by UIP merely come from the
               fact that we are using propositional equality. They are
               independent from the use of reflection but rather coming from
               the proof method used.
             *)
        }

      (* EqTyRefl *)
      - todo.

      (* EqTySym *)
      - todo.

      (* EqTyTrans *)
      - todo.

      (* EqTyIdSubst *)
      - todo.

      (* EqTySubstComp *)
      - todo.

      (* EqTySubstProd *)
      - todo.

      (* EqTySubstId *)
      - { rename A' into IdAuv'.
          intros istG' istIdAuv'.
          todo. (* We need to be able to invert. *)
        }

      (* EqTySubstEmpty *)
      - todo.

      (* EqTySubstUnit *)
      - todo.

      (* EqTySubstBool *)
      - todo.

      (* EqTyExfalso *)
      - todo.

      (* CongProd *)
      - todo.

      (* CongId *)
      - todo.

      (* CongTySubst *)
      - todo.
    }

  (* eval_eqtype_rl *)
  - { destruct Der ; doConfig.

      (* EqTyCtxConv *)
      - todo.

      (* EqTyRefl *)
      - todo.

      (* EqTySym *)
      - todo.

      (* EqTyTrans *)
      - todo.

      (* EqTyIdSubst *)
      - todo.

      (* EqTySubstComp *)
      - todo.

      (* EqTySubstProd *)
      - todo.

      (* EqTySubstId *)
      - todo.

      (* EqTySubstEmpty *)
      - todo.

      (* EqTySubstUnit *)
      - todo.

      (* EqTySubstBool *)
      - todo.

      (* EqTyExfalso *)
      - todo.

      (* CongProd *)
      - todo.

      (* CongId *)
      - todo.

      (* CongTySubst *)
      - todo.
    }
Defined.

Lemma empty_to_empty :
  let Der := (TyEmpty CtxEmpty : pxtt.istype ctxempty Empty) in
  let ist_GG' := istran_ctxempty : istran_ctx ctxempty Datatypes.unit in
  forall xs, projT1 (eval_ty Der ist_GG') xs = Empty_set.
Proof.
  reflexivity.
Qed.

Lemma consistency : forall u, pxtt.isterm ctxempty u Empty -> Empty_set.
Proof.
  intros u Der.
  pose (ist_GG' := istran_ctxempty : istran_ctx ctxempty Datatypes.unit).
  pose (tr := eval_ty (TyEmpty CtxEmpty) ist_GG').
  pose (u' := eval_term Der ist_GG' (projT2 tr)).
  pose (p := u' tt). apply p.
Qed.

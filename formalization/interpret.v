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

Lemma transport_section :
  forall {X Y : Set} (q : X = Y) {A : Family X} (u : section A),
    section (transport _ q A).
Proof.
  intros X Y q A u.
  destruct q.
  exact u.
Defined.


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

with istran_subst' :
  forall (G : context) (G' : Set)
    (D : context) (D' : Set)
    (sbs : substitution) (sbs' : G' -> D'),
    Type
  :=

  | istran_sbzero :
      forall G G' A A' u u',
        istran_ctx G G' ->
        istran_type G G' A A' ->
        istran_term G G' A A' u u' ->
        istran_subst' G G' (ctxextend G A) (sigT A') (sbzero A u)
                     (fun xs => existT _ xs (u' xs))

  | istran_sbweak :
      forall G G' A A',
        istran_ctx G G' ->
        istran_type G G' A A' ->
        istran_subst' (ctxextend G A) (sigT A') G G' (sbweak A)
                     (@projT1 _ _)

  | istran_sbshift :
      forall G G' D D' A A' sbs sbs',
        istran_ctx G G' ->
        istran_ctx D D' ->
        istran_type D D' A A' ->
        istran_subst G G' D D' sbs sbs' ->
        istran_subst'
          (ctxextend G (Subst A sbs)) (sigT (fun xs => A' (sbs' xs)))
          (ctxextend D A) (sigT A')
          (sbshift A sbs) (fun xs => existT _ (sbs' (projT1 xs)) (projT2 xs))

  | istran_sbid :
      forall G G',
        istran_ctx G G' ->
        istran_subst' G G' G G' sbid (fun x => x)

  | istran_sbcomp :
      forall G G' D D' E E' sbs sbs' sbt sbt',
        istran_ctx G G' ->
        istran_ctx D D' ->
        istran_ctx E E' ->
        istran_subst G G' D D' sbs sbs' ->
        istran_subst D D' E E' sbt sbt' ->
        istran_subst' G G' E E'
                     (sbcomp sbt sbs) (fun xs => sbt' (sbs' xs))

with istran_subst :
  forall (G : context) (G' : Set)
    (D : context) (D' : Set)
    (sbs : substitution) (sbs' : G' -> D'),
    Type
  :=

  | istran_SubstCtxConv :
      forall G1 G1' G2 G2' D1 D1' D2 D2' sbs sbs' p q,
        istran_subst' G1 G1' D1 D1' sbs sbs' ->
        istran_eqctx G1 G1' G2 G2' p ->
        istran_eqctx D1 D1' D2 D2' q ->
        istran_subst G2 G2'
                     D2 D2'
                     sbs
                     (fun (xs : G2') => transport _ q (sbs' (transport _ (eq_sym p) xs)))

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

with istran_term'' :
  forall (G : context) (G' : Set)
    (A : type) (A' : Family G')
    (u : term) (u' : section A'),
    Type
  :=

  (* | istran_refl : *)
  (*     forall G G' A A' u u', *)
  (*       istran_term G G' A A' u u' -> *)
  (*       istran_term'' G G' (Id A u u) (Eq A' u' u') (refl A u) (fun xs => eq_refl (u' xs)) *)

  | istran_todo :
      forall G G' A A' u u', istran_term'' G G' A A' u u'

with istran_term' :
  forall (G : context) (G' : Set)
    (A : type) (A' : Family G')
    (u : term) (u' : section A'),
    Type
  :=

  | istran_TermCtxConv :
      forall G G' D D' A A' u u' q,
        istran_term'' G G' A A' u u' ->
        istran_eqctx G G' D D' q ->
        istran_term' D D'
                    A (transport Family q A')
                    u (transport_section q u')

with istran_term :
  forall (G : context) (G' : Set)
    (A : type) (A' : Family G')
    (u : term) (u' : section A'),
    Type
  :=

  | istran_TermTyConv :
      forall G G' A A' B B' u u' p,
        istran_term' G G' A A' u u' ->
        istran_eqtype G G' A A' B B' p ->
        istran_term G G'
                    B B'
                    u (transport _ p u')


with istran_eqctx :
  forall (G : context) (G' : Set)
         (D : context) (D' : Set),
    G' = D' -> Type :=
  | istran_eqctx_todo :
      forall G G' D D' p, istran_eqctx G G' D D' p

with istran_eqtype :
  forall (G : context) (G' : Set)
    (A : type) (A' : Family G')
    (B : type) (B' : Family G'),
    A' = B' -> Type :=
  | istran_eqtype_todo :
      forall G G' A A' B B' p, istran_eqtype G G' A A' B B' p.

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

with cohere_subst' G G' G'' D D' D'' sbs sbs' sbs''
  (H1 : istran_subst' G G'  D D'  sbs sbs')
  (H2 : istran_subst' G G'' D D'' sbs sbs'') {struct H1} :
  existT _ G' (existT _ D' sbs') = existT _ G'' (existT _ D'' sbs'')
    :> { X : Set & { Y : Set & X -> Y } }

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

  (* cohere_subst' *)
  - { todo. }

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
    (G' = D')
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
          eapply (istran_SubstCtxConv G G' G G' (ctxextend G A) (sigT A') (ctxextend G A) (sigT A') _ _ (eq_refl) (eq_refl)).
          - econstructor ; eassumption.
          - constructor.
          - constructor.
        }

      (* SubstWeak *)
      - { destruct (eval_type _ _ i) as (G' & ist_G' & A' & ist_A').
          exists (sigT A').
          split ; [ now constructor | ..].
          exists G'.
          split ; [ assumption | ..].
          eexists.
          eapply (istran_SubstCtxConv (ctxextend G A) (sigT A') (ctxextend G A) (sigT A') G G' G G' _ _ (eq_refl) (eq_refl)).
          - econstructor ; eassumption.
          - constructor.
          - constructor.
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
            eapply (istran_SubstCtxConv (ctxextend G (Subst A sbs)) _ (ctxextend G (Subst A sbs)) _ (ctxextend D A) _ (ctxextend D A) _ _ _ (eq_refl) (eq_refl)).
            + econstructor ; eassumption.
            + constructor.
            + constructor.
        }

      (* SubstId *)
      - { destruct (eval_ctx _ i) as [G' ist_G'].
          exists G'.
          split ; [ assumption | .. ].
          exists G'.
          split ; [ assumption | .. ].
          eexists.
          eapply (istran_SubstCtxConv G _ G _ G _ G _ _ _ (eq_refl) (eq_refl)).
          - econstructor ; eassumption.
          - constructor.
          - constructor.
        }

      (* SubstComp *)
      - { destruct (eval_subst _ _ _ Der1) as
              (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs').
          destruct (eval_subst _ _ _ Der2) as
              (D'' & ist_D'' & E' & ist_E' & sbt' & ist_sbt').
          destruct (cohere_ctx _ _ _ ist_D' ist_D'').
          exists G'. split ; [ assumption | .. ].
          exists E'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_SubstCtxConv G _ G _ E _ E _ _ _ (eq_refl) (eq_refl)).
          - econstructor ; [ .. | eassumption ] ; eassumption.
          - constructor.
          - constructor.
        }

      (* SubstCtxConv *)
      - { destruct (eval_eqctx _ _ e) as
              (G1' & ist_G1' & G2' & ist_G2' & eqG1'G2').
          destruct (eval_eqctx _ _ e0) as
              (D1' & ist_D1' & D2' & ist_D2' & eqD1'D2').
          destruct (eval_subst _ _ _ Der) as
              (G1'' & ist_G1'' & D1'' & ist_D1'' & sbs' & ist_sbs').
          destruct (cohere_ctx _ _ _ ist_D1' ist_D1'').
          destruct (cohere_ctx _ _ _ ist_G1' ist_G1'').
          dependent destruction ist_sbs'.
          destruct p, q.
          exists G2'. split ; [ assumption | .. ].
          exists D2'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_SubstCtxConv _ _ _ _ _ _ _ _ _ _ (eqG1'G2') eqD1'D2').
          - eassumption.
          - constructor.
          - constructor.
        }
  }

  (* Eval_type *)
  - { destruct Der ; doConfig.

      (* TyCtxConv *)
      - { destruct (eval_eqctx _ _ e) as (G' & ist_G' & D' & ist_D' & eqG'D').
          destruct (eval_type _ _ Der) as (G'' & ist_G'' & A' & ist_A').
          destruct (cohere_ctx _ _ _ ist_G' ist_G'').
          exists D'. split ; [ assumption | .. ].
          dependent destruction ist_A'.
          destruct p.
          eexists.
          eapply (istran_TyCtxConv G _ D _ _ _ eqG'D').
          - eassumption.
          - constructor.
        }

      (* TySubst *)
      - { destruct (eval_subst _ _ _ i) as
              (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs').
          destruct (eval_type _ _ Der) as (D'' & ist_D'' & A' & ist_A'').
          destruct (cohere_ctx _ _ _ ist_D' ist_D'').
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G _ G _ _ _ (eq_refl)).
          - econstructor ; eassumption.
          - constructor.
        }

      (* TyProd *)
      - { destruct (eval_type _ _ i) as (G' & ist_G' & A' & ist_A').
          destruct (eval_type _ _ Der) as (GA'' & ist_GA'' & B' & ist_B').
          pose (ist_GA' := istran_ctxextend _ _ _ _ ist_G' ist_A').
          destruct (cohere_ctx _ _ _ ist_GA' ist_GA'').
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G _ G _ _ _ (eq_refl)).
          - econstructor ; eassumption.
          - constructor.
        }

      (* TyId *)
      - { destruct (eval_term _ _ _ i1)
            as (G' & istG' & A' & istA' & u' & istu').
          destruct (eval_term _ _ _ i2)
            as (G'' & istG'' & A'' & istA'' & v' & istv').
          (* destruct (cohere_ctx _ _ _ istG' istG''). *)
          pose (p := cohere_type _ _ _ _ _ _ istA' istA'').
          destruct (path_decompose_existT p) as [q r].
          destruct q. simpl in *.
          destruct r.
          clear p.
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G _ G _ _ _ (eq_refl)).
          - econstructor ; eassumption.
          - constructor.
        }

      (* TyEmpty *)
      - { destruct (eval_ctx _ i) as (G' & istG').
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G _ G _ _ _ (eq_refl)).
          - econstructor ; eassumption.
          - constructor.
        }

      (* TyUnit *)
      - { destruct (eval_ctx _ i) as (G' & istG').
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G _ G _ _ _ (eq_refl)).
          - econstructor ; eassumption.
          - constructor.
        }

      (* TyBool *)
      - { destruct (eval_ctx _ i) as (G' & istG').
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G _ G _ _ _ (eq_refl)).
          - econstructor ; eassumption.
          - constructor.
        }
    }

    (* eval_term *)
  - { destruct Der ; doConfig.

      (* TermTyConv *)
      - todo.

      (* TermCtxConv *)
      - todo.

      (* TermSubst *)
      - todo.

      (* TermVarZero *)
      - todo.

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

  (* eval_eqctx *)
  - { destruct Der ; doConfig.

      (* CtxRefl *)
      - { destruct (eval_ctx _ i) as (G' & istG').
          exists G'. split ; [ assumption | .. ].
          exists G'. split ; [ assumption | .. ].
          reflexivity.
        }

      (* CtxSym *)
      - { destruct (eval_eqctx _ _ Der) as (G' & istG' & D' & istD' & eq).
          exists D'. split ; [ assumption | .. ].
          exists G'. split ; [ assumption | .. ].
          symmetry. assumption.
        }

      (* CtxTrans *)
      - { destruct (eval_eqctx _ _ Der1) as (G' & istG' & D' & istD' & eq1).
          destruct (eval_eqctx _ _ Der2) as (D'' & istD'' & E' & istE' & eq2).
          destruct (cohere_ctx _ _ _ istD' istD'').
          exists G'. split ; [ assumption | .. ].
          exists E'. split ; [ assumption | .. ].
          transitivity D' ; assumption.
        }

      (* EqCtxEmpty *)
      - { eexists. split ; [ econstructor | .. ].
          eexists. split ; [ econstructor | .. ].
          reflexivity.
        }

      (* EqCtxExtend *)
      - { destruct (eval_eqctx _ _ Der) as (G' & istG' & D' & istD' & eqGD).
          destruct (eval_eqtype _ _ _ e)
            as (G'' & istG'' & A' & istA' & B' & istB' & eqAB).
          destruct (cohere_ctx _ _ _ istG' istG'').
          exists (sigT A'). split ; [ now constructor | .. ].
          exists (sigT (transport Family eqGD B')). split.
          - constructor.
            + assumption.
            + dependent destruction istB'.
              destruct p.
              now apply (istran_TyCtxConv G).
          - destruct eqAB.
            destruct eqGD.
            reflexivity.
        }
    }

  (* eval_eqtype *)
  - { destruct Der ; doConfig.

      (* EqTyCtxConv *)
      - {
          destruct (eval_eqctx _ _ e) as (G' & ist_G' & D' & ist_D' & eq_G'D').
          destruct (eval_eqtype _ _ _ Der) as (G'' & ist_G'' & A' & ist_A' & B' & ist_B' & eq_A'B').
          destruct (cohere_ctx _ _ _ ist_G' ist_G'').
          exists D'. split ; [ assumption | ..].
          exists (transport Family eq_G'D' A'). split.
          - dependent destruction ist_A'.
            destruct p.
            now apply (istran_TyCtxConv G).
          - exists (transport Family eq_G'D' B'). split.
            + dependent destruction ist_B'.
              destruct p.
              now apply (istran_TyCtxConv G).
            + destruct eq_A'B'.
              reflexivity.
        }

      (* EqTyRefl *)
      - { destruct (eval_type _ _ i0) as (G' & ist_G' & A' & ist_A').
          exists G'. split ; [ assumption | ..].
          exists A'. split ; [ assumption | ..].
          exists A'. split ; [ assumption | ..].
          reflexivity.
        }


      (* EqTySym *)
      - { destruct (eval_eqtype _ _ _ Der) as (G' & ist_G' & A' & ist_A' & B' & ist_B' & eq_A'B').
          exists G'. split ; [ assumption | ..].
          exists B'. split ; [ assumption | ..].
          exists A'. split ; [ assumption | ..].
          now symmetry.
        }

      (* EqTyTrans *)
      - { destruct (eval_eqtype _ _ _ Der1) as (G' & ist_G' & A' & ist_A' & B' & ist_B' & eq_A'B').
          destruct (eval_eqtype _ _ _ Der2) as (G'' & ist_G'' & B'' & ist_B'' & C' & ist_C' & eq_B''C').
          pose (p := cohere_type _ _ _ _ _ _ ist_B' ist_B'').
          destruct (path_decompose_existT p) as [q r].
          destruct q.
          simpl in r. destruct r.
          exists G'. split ; [ assumption | ..].
          exists A'. split ; [ assumption | ..].
          exists C'. split ; [ assumption | ..].
          now transitivity B'.
        }

      (* EqTyIdSubst *)
      - { destruct (eval_type _ _ i0) as (G' & ist_G' & A' & ist_A').
          exists G'. split ; [ assumption | ..].
          exists A'. split.
          - apply (istran_TyCtxConv G G' G G' _ _ eq_refl).
            + eapply istran_Subst.
              * eassumption.
              * apply (istran_SubstCtxConv
                         G G' G G'
                         G G' G G'
                         sbid (fun xs => xs)
                         eq_refl eq_refl) ;
                  now constructor.
            + now constructor.
          - exists A'. split ; [ assumption | reflexivity ].
        }

      (* EqTySubstComp *)
      - { destruct (eval_type _ _ i) as (E' & ist_E' & A' & ist_A').
          destruct (eval_subst _ _ _ i0) as (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs').
          destruct (eval_subst _ _ _ i1) as (D'' & ist_D'' & E'' & ist_E'' & sbt' & ist_sbt').
          destruct (cohere_ctx _ _ _ ist_D' ist_D'').
          destruct (cohere_ctx _ _ _ ist_E' ist_E'').
          exists G'. split ; [ assumption | ..].
          exists (fun xs => A' (sbt' (sbs' xs))). split.
          - apply (istran_TyCtxConv G G' _ _ _ _ eq_refl) ; [ .. | constructor].
            apply (istran_Subst _ _ D D' _ (fun ys => A' (sbt' ys)) sbs sbs').
            + apply (istran_TyCtxConv D D' _ _ _ _ eq_refl) ; [ .. | constructor].
              econstructor ; eassumption.
            + assumption.
          - exists (fun xs => A' (sbt' (sbs' xs))). split.
            + apply (istran_TyCtxConv G G' _ _ _ _ eq_refl) ; [ .. | constructor].
              apply (istran_Subst _ _ E E' _ _).
              * assumption.
              * apply (istran_SubstCtxConv
                         G G' G G'
                         E E' E E'
                         _ (fun xs : G' => sbt' (sbs' xs))
                         eq_refl eq_refl) ; [ idtac | constructor ..].
                econstructor ; eassumption.
            + reflexivity.
      }

      (* EqTySubstProd *)
      - todo.

      (* EqTySubstId *)
      - todo.

      (* EqTySubstEmpty *)
      - { destruct (eval_subst _ _ _ i) as (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs').
          exists G'. split ; [ assumption | ..].
          exists (fun xs => Empty_set). split.
          - apply (istran_TyCtxConv G G' _ _ _ _ eq_refl) ; [.. | constructor].
            apply (istran_Subst _ _ D D' _ (fun ys => Empty_set) sbs sbs') ;
              [ .. | assumption].
            apply (istran_TyCtxConv D D' _ _ _ _ eq_refl) ; [.. | constructor].
            now constructor.
          - exists (fun xs => Empty_set). split.
            + apply (istran_TyCtxConv G G' _ _ _ _ eq_refl) ; [.. | constructor].
              now constructor.
            + reflexivity.
        }

      (* EqTySubstUnit *)
      - { destruct (eval_subst _ _ _ i) as (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs').
          exists G'. split ; [ assumption | ..].
          exists (fun xs => Datatypes.unit). split.
          - apply (istran_TyCtxConv G G' _ _ _ _ eq_refl) ; [.. | constructor].
            apply (istran_Subst _ _ D D' _ (fun ys => Datatypes.unit) sbs sbs') ;
              [ .. | assumption].
            apply (istran_TyCtxConv D D' _ _ _ _ eq_refl) ; [.. | constructor].
            now constructor.
          - exists (fun xs => Datatypes.unit). split.
            + apply (istran_TyCtxConv G G' _ _ _ _ eq_refl) ; [.. | constructor].
              now constructor.
            + reflexivity.
        }

      (* EqTySubstBool *)
      - { destruct (eval_subst _ _ _ i) as (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs').
          exists G'. split ; [ assumption | ..].
          exists (fun xs => bool). split.
          - apply (istran_TyCtxConv G G' _ _ _ _ eq_refl) ; [.. | constructor].
            apply (istran_Subst _ _ D D' _ (fun ys => bool) sbs sbs') ;
              [ .. | assumption].
            apply (istran_TyCtxConv D D' _ _ _ _ eq_refl) ; [.. | constructor].
            now constructor.
          - exists (fun xs => bool). split.
            + apply (istran_TyCtxConv G G' _ _ _ _ eq_refl) ; [.. | constructor].
              now constructor.
            + reflexivity.
        }

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
  forall xs, projT1 (eval_type Der ist_GG') xs = Empty_set.
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

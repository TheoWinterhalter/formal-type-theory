Require Import Coq.Program.Equality.

Require config.
Require Import config_tactics.

Local Open Scope type_scope.

Require Import syntax. (* The syntax of ett/ptt. *)
Require Import tt.

Require ptt ett ptt_sanity ett2ptt ptt2ett uniqueness ptt_inversion.
Require Import tactics.
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

Lemma transport_path {X : Type} (P : X -> Type) {x y : X}
      {a b : P x} (p : x = y) :
  a = b -> transport P p a = transport P p b.
Proof.
  intro q.
  destruct p.
  exact q.
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
        pxtt.istype G A ->
        istran_ctx G G' ->
        istran_type G G' A A' ->
        istran_ctx (ctxextend G A) (sigT A')

with istran_subst'' :
  forall (G : context) (G' : Set)
    (D : context) (D' : Set)
    (sbs : substitution) (sbs' : G' -> D'),
    Type
  :=

  | istran_sbzero :
      forall G G' A A' u u',
        pxtt.isterm G u A ->
        istran_ctx G G' ->
        istran_type G G' A A' ->
        istran_term G G' A A' u u' ->
        istran_subst'' G G' (ctxextend G A) (sigT A') (sbzero A u)
                     (fun xs => existT _ xs (u' xs))

  | istran_sbweak :
      forall G G' A A',
        pxtt.istype G A ->
        istran_ctx G G' ->
        istran_type G G' A A' ->
        istran_subst'' (ctxextend G A) (sigT A') G G' (sbweak A)
                     (@projT1 _ _)

  | istran_sbshift :
      forall G G' D D' A A' sbs sbs',
        pxtt.issubst sbs G D ->
        pxtt.istype D A ->
        istran_ctx G G' ->
        istran_ctx D D' ->
        istran_type D D' A A' ->
        istran_subst G G' D D' sbs sbs' ->
        istran_subst''
          (ctxextend G (Subst A sbs)) (sigT (fun xs => A' (sbs' xs)))
          (ctxextend D A) (sigT A')
          (sbshift A sbs) (fun xs => existT _ (sbs' (projT1 xs)) (projT2 xs))

  | istran_sbid :
      forall G G',
        pxtt.isctx G ->
        istran_ctx G G' ->
        istran_subst'' G G' G G' sbid (fun x => x)

  | istran_sbcomp :
      forall G G' D D' E E' sbs sbs' sbt sbt',
        pxtt.issubst sbs G D ->
        pxtt.issubst sbt D E ->
        istran_ctx G G' ->
        istran_ctx D D' ->
        istran_ctx E E' ->
        istran_subst G G' D D' sbs sbs' ->
        istran_subst D D' E E' sbt sbt' ->
        istran_subst'' G G' E E'
                     (sbcomp sbt sbs) (fun xs => sbt' (sbs' xs))

with istran_subst' :
  forall (G : context) (G' : Set)
    (D : context) (D' : Set)
    (sbs : substitution) (sbs' : G' -> D'),
    Type
  :=

  | istran_SubstCtxConv_left :
      forall G1 G2 G1' G2' D D' sbs sbs' p,
        pxtt.issubst sbs G2 D ->
        pxtt.eqctx G1 G2 ->
        istran_ctx G1 G1' ->
        istran_ctx G2 G2' ->
        istran_ctx D D' ->
        istran_eqctx G1 G1' G2 G2' p ->
        istran_subst'' G1 G1' D D' sbs sbs' ->
        istran_subst' G2 G2' D D' sbs (transport (fun (G' : Set) => G' -> D') p sbs')

with istran_subst :
  forall (G : context) (G' : Set)
    (D : context) (D' : Set)
    (sbs : substitution) (sbs' : G' -> D'),
    Type
  :=

  | istran_SubstCtxConv_right :
      forall G G' D1 D2 D1' D2' sbs sbs' q,
        pxtt.issubst sbs G D1 ->
        pxtt.eqctx D1 D2 ->
        istran_ctx G G' ->
        istran_ctx D1 D1' ->
        istran_ctx D2 D2' ->
        istran_eqctx D1 D1' D2 D2' q ->
        istran_subst' G G' D1 D1' sbs sbs' ->
        istran_subst G G' D2 D2' sbs (transport (fun (D' : Set) => G' -> D') q sbs')

with istran_type' :
  (forall (G : context) (G' : Set) (A : type) (A' : Family G'), Type) :=

 | istran_Prod :
     forall G G' A A' B B',
       pxtt.istype G A ->
       pxtt.istype (ctxextend G A) B ->
       istran_type G G' A A' ->
       istran_type (ctxextend G A) (sigT A') B B' ->
       istran_type' G G' (Prod A B) (Pi A' B')

 | istran_Id :
     forall G G' A A' u u' v v',
       pxtt.isterm G u A ->
       pxtt.isterm G v A ->
       istran_type G G' A A' ->
       istran_term G G' A A' u u' ->
       istran_term G G' A A' v v' ->
       istran_type' G G' (Id A u v) (Eq A' u' v')

 | istran_Subst :
     forall G G' D D' A A' sbs sbs',
       pxtt.issubst sbs G D ->
       pxtt.istype D A ->
       istran_type D D' A A' ->
       istran_subst G G' D D' sbs sbs' ->
       istran_type' G G' (Subst A sbs) (fun xs => A' (sbs' xs))

 | istran_Empty :
     forall G G',
       pxtt.isctx G ->
       istran_ctx G G' ->
       istran_type' G G' Empty (fun _ => Empty_set)

 | istran_Unit :
     forall G G',
       pxtt.isctx G ->
       istran_ctx G G' ->
       istran_type' G G' Unit (fun _ => Datatypes.unit)

 | istran_Bool :
     forall G G',
       pxtt.isctx G ->
       istran_ctx G G' ->
       istran_type' G G' Bool (fun _ => Datatypes.bool)

with istran_type :
       (forall (G : context) (G' : Set) (A : type) (A' : Family G'), Type) :=

 | istran_TyCtxConv :
     forall G1 G2 G' A A',
       pxtt.eqctx G1 G2 ->
       pxtt.istype G1 A ->
       istran_type' G1 G' A A' ->
       istran_type G2 G' A A'

with istran_term'' :
  forall (G : context) (G' : Set)
    (A : type) (A' : Family G')
    (u : term) (u' : section A'),
    Type
  :=

  (* It can't be called istran_subst, so we use the name of the rule *)
  | istran_TermSubst :
      forall G G' D D' A A' u u' sbs sbs',
        pxtt.issubst sbs G D ->
        pxtt.isterm D u A ->
        istran_subst G G' D D' sbs sbs' ->
        istran_term D D' A A' u u' ->
        istran_term'' G G'
                      (Subst A sbs) (fun xs => A' (sbs' xs))
                      (subst u sbs) (fun xs => u' (sbs' xs))

  | istran_TermVarZero :
      forall G G' A A',
        pxtt.istype G A ->
        istran_type G G' A A' ->
        istran_term'' (ctxextend G A) (sigT A')
                      (Subst A (sbweak A)) (fun xs => A' ((@projT1 _ _) xs))
                      (var 0) (fun xs => projT2 xs)

  | istran_TermVarSucc :
      forall G G' A A' B B' k vk',
        pxtt.isterm G (var k) A ->
        pxtt.istype G B ->
        istran_term G G' A A' (var k) vk' ->
        istran_type G G' B B' ->
        istran_term'' (ctxextend G B) (sigT B')
                      (Subst A (sbweak B)) (fun xs => A' ((@projT1 _ _) xs))
                      (var (S k)) (fun xs => vk' ((@projT1 _ _) xs))

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
      forall G1 G2 G' A A' u u',
        pxtt.eqctx G1 G2 ->
        istran_term'' G1 G' A A' u u' ->
        istran_term' G2 G' A A' u u'

with istran_term :
  forall (G : context) (G' : Set)
    (A : type) (A' : Family G')
    (u : term) (u' : section A'),
    Type
  :=

  | istran_TermTyConv :
      forall G G' A1 A2 A' u u',
        pxtt.eqtype G A1 A2 ->
        istran_term' G G' A1 A' u u' ->
        istran_term G G' A2 A' u u'

with istran_eqctx :
  forall (G : context) (G' : Set)
    (D : context) (D' : Set)
    (p : G' = D'),
    Type
  :=

  | istran_eqctx_always :
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

(*
Fixpoint cohere_ctx G1 G2 G1' G2'
  (eqG12 : pxtt.eqctx G1 G2)
  (H1 : istran_ctx G1 G1')
  (H2 : istran_ctx G2 G2') {struct H1} :
  G1' = G2'

with cohere_subst' G1 G2 G1' G2' D1 D2 D1' D2' sbs1 sbs2 sbs1' sbs2'
  (eqG12 : pxtt.eqctx G1 G2)
  (eqD12 : pxtt.eqctx D1 D2)
  (eqsbs12 : pxtt.eqsubst sbs1 sbs2 G1 G2)
  (H1 : istran_subst' G1 G1'  D1 D1'  sbs1 sbs1')
  (H2 : istran_subst' G2 G2' D2 D2' sbs2 sbs2') {struct H1} :
  existT _ G1' (existT _ D1' sbs1') = existT _ G2' (existT _ D2' sbs2')
    :> { X : Set & { Y : Set & X -> Y } }

with cohere_subst G1 G2 G1' G2' D1 D2 D1' D2' sbs1 sbs2 sbs1' sbs2'
  (eqG12 : pxtt.eqctx G1 G2)
  (eqD12 : pxtt.eqctx D1 D2)
  (eqsbs12 : pxtt.eqsubst sbs1 sbs2 G1 G2)
  (H1 : istran_subst' G1 G1'  D1 D1'  sbs1 sbs1')
  (H2 : istran_subst' G2 G2' D2 D2' sbs2 sbs2') {struct H1} :
  existT _ G1' (existT _ D1' sbs1') = existT _ G2' (existT _ D2' sbs2')
    :> { X : Set & { Y : Set & X -> Y } }

with cohere_type' G1 G2 G1' G2' A1 A2 A1' A2'
  (eqG12 : pxtt.eqctx G1 G2)
  (eqA12 : pxtt.eqtype G1 A1 A2)
  (H1 : istran_type' G1 G1' A1 A1')
  (H2 : istran_type' G2 G2' A2 A2') {struct H1} :
  existT _ G1' A1' = existT _ G2' A2' :> sigT Family

with cohere_type G1 G2 G1' G2' A1 A2 A1' A2'
  (eqG12 : pxtt.eqctx G1 G2)
  (eqA12 : pxtt.eqtype G1 A1 A2)
  (H1 : istran_type G1 G1' A1 A1')
  (H2 : istran_type G2 G2' A2 A2') {struct H1} :
  existT _ G1' A1' = existT _ G2' A2' :> sigT Family

with cohere_term G1 G2 G1' G2' A1 A2 A1' A2' u1 u2 u1' u2'
  (eqG12 : pxtt.eqctx G1 G2)
  (eqA12 : pxtt.eqtype G1 A1 A2)
  (equ12 : pxtt.eqterm G1 u1 u2 A1)
  (H1 : istran_term G1 G1' A1 A1' u1 u1')
  (H2 : istran_term G2 G2' A2 A2' u2 u2') {struct H1} :
  existT _ G1' (existT _ A1' u1') = existT _ G2' (existT _ A2' u2')
    :> { X : Set & { F : Family X & section F } }
.

Proof.
  (* cohere_ctx *)
  - { destruct H1 ;
      dependent destruction H2.

      (* ctxempty *)
      - { reflexivity. }

      (* ctxextend *)
      - {
          rename
            G'0 into G'',
            A'0 into A''.
            apply (path_sigT (existT _ G' A') (existT _ G'' A'')).
            apply (cohere_type G G G' G'' A A' A'') ; [ idtac | assumption ..].
            capply CtxRefl.
            now apply (ptt_sanity.sane_istype G A).
        }
    }

  (* cohere_subst' *)
  - { destruct H1 ;
      dependent destruction H2.

     (* sbzero *)
     - { rename G into G1, G0 into G2, G'0 into G'', A'0 into A'', u'0 into u''.
         assert (eqAA : pxtt.eqtype G1 A A).
         { capply EqTyRefl ; now apply (ptt_sanity.sane_isterm _ _ _ i). }
         pose (p := cohere_term _ _ _ _ _ _ _ _ _ _ _ eqG12 eqAA i2 i6).
         destruct (path_decompose_existT p) as [q r].
         destruct q ; simpl in r.
         destruct (path_decompose_existT r) as [qq rr].
         destruct qq ; simpl in rr.
         destruct rr.
         reflexivity.
       }

     (* sbweak *)
     - { rename G'0 into G'', A'0 into A''.
         pose (p := cohere_type _ _ _ _ _ _ _ eqD12 i1 i4).
         destruct (path_decompose_existT p) as [q r].
         destruct q ; simpl in r.
         destruct r.
         reflexivity.
       }

     (* sbshift *)
     - { rename G into G1, G0 into G2, eqG12 into eqextG12,
                D into D1, D0 into D2, D'0 into D'', G'0 into G'', A'0 into A'',
                sbs'0 into sbs'', eqD12 into eqextD12.
         assert (eqD12 : pxtt.eqctx D1 D2).
         { apply ett2ptt.sane_eqctx.
           apply (uniqueness.eqctx_ctxextend D1 A D2 A).
           now apply ptt2ett.sane_eqctx.
         }
         assert (eqG12 : pxtt.eqctx G1 G2).
         { apply ett2ptt.sane_eqctx.
           apply (uniqueness.eqctx_ctxextend G1 (Subst A sbs) G2 (Subst A sbs)).
           now apply ptt2ett.sane_eqctx.
         }
         pose (p := cohere_subst G1 G2 _ _ D1 D2 _ _ _ _ _ eqG12 eqD12 i4 i10).
         destruct (path_decompose_existT p) as [q r].
         destruct q ; simpl in r.
         destruct (path_decompose_existT r) as [qq rr].
         destruct qq ; simpl in rr.
         destruct rr.
         pose (pp := cohere_type D1 D2 _ _ A A' A'' eqD12 i3 i9).
         destruct (path_decompose_existT pp) as [qq rr].
         rewrite (UIP_Set qq) in rr.
         simpl in rr ; destruct rr.
         reflexivity.
       }

     (* sbid *)
     - { rename G into G1, G0 into G2, G'0 into G''.
         (* XXX we are stuck here because i0 and i2 have different contexts. *)
         todo.
       }

     (* sbcomp *)
     - {
         rename D into D1, D0 into D2, E into E1, E0 into E2, D'0 into D'', E'0 into E'',
                G'0 into G'', sbs'0 into sbs'', sbt'0 into sbt''.
         pose (p := cohere_subst _ _ _ _ _ _ _ _ _ _ eqD12 i5 i12).
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
          rename D into D1, D0 into D2, D' into D1', D'0 into D2',
                 G'0 into G'', A'0 into A'', sbs'0 into sbs''.
          assert (eqctx_GG : pxtt.eqctx G G).
          { capply CtxRefl. apply (ptt_sanity.sane_issubst _ _ _ i). }
          pose (eqctx_D1D2' := uniqueness.unique_subst _ _ _ i _ _ i2 eqctx_GG).
          pose (eqctx_D1D2 := ett2ptt.sane_eqctx _ _ eqctx_D1D2').

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

*)

Lemma istran_subst''_subst {G G' D D' sbs sbs'} :
  pxtt.issubst sbs G D ->
  istran_ctx G G' ->
  istran_ctx D D' ->
  istran_subst'' G G' D D' sbs sbs' ->
  istran_subst   G G' D D' sbs sbs'.
Proof.
  intros pistsbs istG istD istsbs.
  apply (istran_SubstCtxConv_right G G' D D D' D' sbs sbs' eq_refl) ;
    try assumption.
  - capply CtxRefl.
    apply (ptt_sanity.sane_issubst _ _ _ pistsbs).
  - constructor.
  - apply (istran_SubstCtxConv_left G G G' G' D D' sbs sbs' eq_refl) ;
      try assumption.
    + capply CtxRefl.
      apply (ptt_sanity.sane_issubst _ _ _ pistsbs).
    + constructor.
Defined.


Fixpoint eval_ctx G (Der : pxtt.isctx G) {struct Der} :
  { G' : Set & istran_ctx G G' }

with eval_subst {G G' D sbs} (Der : pxtt.issubst sbs G D) {struct Der} :
  istran_ctx G G' ->
  { D' : Set &
    istran_ctx D D' * {
    sbs' : G' -> D' &
    istran_subst G G' D D' sbs sbs'
  } }

with eval_type {G G' A} (Der : pxtt.istype G A) {struct Der} :
  istran_ctx G G' ->
  { A' : Family G' & istran_type G G' A A'}

with eval_term {G G' A A' u} (Der : pxtt.isterm G u A) {struct Der} :
 istran_ctx G G' ->
 istran_type G G' A A' ->
 { u' : section A' & istran_term G G' A A' u u' }

with eval_eqctx {G G' D D'} (Der : pxtt.eqctx G D) {struct Der} :
  istran_ctx G G' ->
  istran_ctx D D' ->
  G' = D'

with eval_eqtype {G G' A A' B B'} (Der : pxtt.eqtype G A B) {struct Der} :
  istran_ctx G G' ->
  istran_type G G' A A' ->
  istran_type G G' B B' ->
  A' = B'

with eval_eqterm {G G' A A' u u' v v'} (Der : pxtt.eqterm G u v A) {struct Der} :
  istran_ctx G G' ->
  istran_type G G' A A' ->
  istran_term G G' A A' u u' ->
  istran_term G G' A A' v v' ->
  u' = v'.

Proof.
  (* eval_ctx *)
  - { destruct Der ; doConfig.

      (* CtxEmpty *)
      - exists Datatypes.unit.
        constructor.

      (* CtxExtend *)
      - { destruct (eval_ctx _ i) as (G' & istG' ).
          destruct (eval_type _ G' _ i0 istG') as (A' & istA').
          exists (sigT A').
          now constructor.
        }
    }

  (* eval_subst *)
  - { intro istG'.
      destruct Der ; doConfig.

      (* SubstZero *)
      - { destruct (eval_type _ G' _ i0 istG') as (A' & istA').
          destruct (eval_term _ _ _ _ _ i istG' istA') as (u' & istu').
          exists (sigT A').
          split ; [ now constructor | ..].
          eexists.
          eapply istran_subst''_subst.
          - now constructor.
          - assumption.
          - now constructor.
          - econstructor ; eassumption.
        }

      (* SubstWeak *)
      - { rename G' into GA', istG' into istGA'.
          inversion istGA'. subst.
          rename X0 into istG', X1 into istA'.

          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply istran_subst''_subst.
          - now constructor.
          - assumption.
          - assumption.
          - econstructor ; assumption.
        }

      (* SubstShift *)
      - { rename G' into GAs', istG' into istGAs'.
          inversion istGAs'. subst.
          rename A' into As', X0 into istG', X1 into istAs'.
          inversion istAs'. subst.
          rename A' into As'', X2 into istAs''.
          inversion istAs''. subst.
          destruct (path_decompose_existT H5).
          (* Removing the 'subst' before doesn't help in destructing the
             equality G' = G'.
           *)

          (* exists (sigT A'0). split. *)
          (* - constructor. *)
          (*   + assumption. *)
          (*   + *)
          (* We have D0 where we would like to have D... *)
          todo.



          (* destruct (eval_subst _ _ _ Der) as *)
          (*     (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs'). *)
          (* destruct (eval_type _ _ i) as (D'' & ist_D'' & A' & ist_A'). *)
          (* destruct (cohere_ctx _ _ _ ist_D' ist_D''). *)
          (* exists (sigT (fun xs => A' (sbs' xs))). *)
          (* split. *)
          (* - constructor. *)
          (*   + assumption. *)
          (*   + apply (istran_TyCtxConv G G). *)
          (*     * now capply CtxRefl. *)
          (*     * econstructor ; eassumption. *)
          (* - exists (sigT A'). *)
          (*   split ; [ now constructor | ..]. *)
          (*   eexists. *)
          (*   apply (istran_SubstCtxConv (ctxextend G (Subst A sbs)) (ctxextend G (Subst A sbs)) _ (ctxextend D A) (ctxextend D A) _). *)
          (*   + capply CtxRefl. capply CtxExtend. *)
          (*     * assumption. *)
          (*     * ceapply TySubst ; eassumption. *)
          (*   + capply CtxRefl. now capply CtxExtend. *)
          (*   + econstructor ; eassumption. *)
        }

      (* SubstId *)
      - { exists G'. split ; [ assumption | .. ].
          eexists.
          eapply istran_subst''_subst.
          - now constructor.
          - assumption.
          - assumption.
          - econstructor ; assumption.
        }

      (* SubstComp *)
      - { destruct (eval_subst _ G' _ _ Der1 istG')
            as (D' & istD' & sbs' & ist_sbs').
          destruct (eval_subst _ D' _ _ Der2 istD')
            as (E' & istE' & sbt' & ist_sbt').
          exists E'. split ; [ assumption | .. ].
          eexists.
          eapply istran_subst''_subst.
          - ceapply SubstComp ; eassumption.
          - assumption.
          - assumption.
          - econstructor ; eassumption.
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
          exists G2'. split ; [ assumption | .. ].
          exists D2'. split ; [ assumption | .. ].
          destruct eqG1'G2'.
          destruct eqD1'D2'.
          exists sbs'.
          eapply (istran_SubstCtxConv G1 G2 _ D1 D2 _).
          - (config eapply @CtxTrans with (D := G0)) ; [ idtac | assumption ..].
            now apply (ptt_sanity.sane_eqctx G1 G0).
          - (config eapply @CtxTrans with (D := D0)) ; [ idtac | assumption ..].
            now apply (ptt_sanity.sane_eqctx D1 D0).
          - assumption.
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
          destruct eqG'D'.
          exists A'.
          apply (istran_TyCtxConv G1 D _).
          - (config eapply @CtxTrans with (D := G2)) ; [ idtac | assumption ..].
            now apply (ptt_sanity.sane_eqctx G1 G2).
          - assumption.
        }

      (* TySubst *)
      - { destruct (eval_subst _ _ _ i) as
              (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs').
          destruct (eval_type _ _ Der) as (D'' & ist_D'' & A' & ist_A'').
          destruct (cohere_ctx _ _ _ ist_D' ist_D'').
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G G _).
          - now capply CtxRefl.
          - econstructor ; eassumption.
        }

      (* TyProd *)
      - { destruct (eval_type _ _ i) as (G' & ist_G' & A' & ist_A').
          destruct (eval_type _ _ Der) as (GA'' & ist_GA'' & B' & ist_B').
          pose (ist_GA' := istran_ctxextend _ _ _ _ ist_G' ist_A').
          destruct (cohere_ctx _ _ _ ist_GA' ist_GA'').
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G G _).
          - now capply CtxRefl.
          - econstructor ; eassumption.
        }

      (* TyId *)
      - { destruct (eval_term _ _ _ i1)
            as (G' & istG' & A' & istA' & u' & istu').
          destruct (eval_term _ _ _ i2)
            as (G'' & istG'' & A'' & istA'' & v' & istv').
          pose (p := cohere_type _ _ _ _ _ _ istA' istA'').
          destruct (path_decompose_existT p) as [q r].
          destruct q. simpl in *.
          destruct r.
          clear p.
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G G _).
          - now capply CtxRefl.
          - econstructor ; eassumption.
        }

      (* TyEmpty *)
      - { destruct (eval_ctx _ i) as (G' & istG').
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G G _).
          - now capply CtxRefl.
          - econstructor ; eassumption.
        }

      (* TyUnit *)
      - { destruct (eval_ctx _ i) as (G' & istG').
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G G _).
          - now capply CtxRefl.
          - econstructor ; eassumption.
        }

      (* TyBool *)
      - { destruct (eval_ctx _ i) as (G' & istG').
          exists G'. split ; [ assumption | .. ].
          eexists.
          eapply (istran_TyCtxConv G G _).
          - now capply CtxRefl.
          - econstructor ; eassumption.
        }
    }

    (* eval_term *)
  - { destruct Der ; doConfig.

      (* TermTyConv *)
      - todo.

      (* TermCtxConv *)
      - todo.

      (* TermSubst *)
      - {

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
              destruct eqGD.
              apply (istran_TyCtxConv G1 D).
              * (config eapply @CtxTrans with (D := G2)) ; [ idtac | assumption ..].
                now apply (ptt_sanity.sane_eqctx G1 G2).
              * assumption.
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
          destruct eq_G'D'.
          exists A'. split.
          - dependent destruction ist_A'.
            apply (istran_TyCtxConv G1).
            + (config eapply @CtxTrans with (D := G2)) ; [ idtac | assumption ..].
              now apply (ptt_sanity.sane_eqctx G1 G2).
            + assumption.
          - exists B'. split.
            + dependent destruction ist_B'.
              apply (istran_TyCtxConv G1).
              * (config eapply @CtxTrans with (D := G2)) ; [ idtac | assumption ..].
                now apply (ptt_sanity.sane_eqctx G1 G2).
              * assumption.
            + exact eq_A'B'.
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
          - apply (istran_TyCtxConv G G).
            + now capply CtxRefl.
            + eapply istran_Subst.
              * eassumption.
              * apply (istran_SubstCtxConv
                         G G G'
                         G G G'
                         sbid (fun xs => xs)) ;
                  now constructor.
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
          - apply (istran_TyCtxConv G G _) ; [now capply CtxRefl | ..].
            apply (istran_Subst _ _ D D' _ (fun ys => A' (sbt' ys)) sbs sbs').
              + apply (istran_TyCtxConv D D _) ; [now capply CtxRefl | ..].
                econstructor ; eassumption.
              + assumption.
          - exists (fun xs => A' (sbt' (sbs' xs))). split.
            + apply (istran_TyCtxConv G G _) ; [now capply CtxRefl | ..].
              apply (istran_Subst _ _ E E' _ _).
              * assumption.
              * apply (istran_SubstCtxConv
                         G G G'
                         E E E'
                         _ (fun xs : G' => sbt' (sbs' xs))) ; [now capply CtxRefl | now capply CtxRefl | ..].
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
          - apply (istran_TyCtxConv G) ; [ now capply CtxRefl | ..].
            apply (istran_Subst _ _ D D' _ (fun ys => Empty_set) sbs sbs') ;
              [ .. | assumption].
            apply (istran_TyCtxConv D) ; [ now capply CtxRefl | ..].
            now constructor.
          - exists (fun xs => Empty_set). split.
            + apply (istran_TyCtxConv G) ; [ now capply CtxRefl | ..].
              now constructor.
            + reflexivity.
        }

      (* EqTySubstUnit *)
      - { destruct (eval_subst _ _ _ i) as (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs').
          exists G'. split ; [ assumption | ..].
          exists (fun xs => Datatypes.unit). split.
          - apply (istran_TyCtxConv G) ; [ now capply CtxRefl | ..].
            apply (istran_Subst _ _ D D' _ (fun ys => Datatypes.unit) sbs sbs') ;
              [ .. | assumption].
            apply (istran_TyCtxConv D) ; [ now capply CtxRefl | ..].
            now constructor.
          - exists (fun xs => Datatypes.unit). split.
            + apply (istran_TyCtxConv G) ; [ now capply CtxRefl | ..].
              now constructor.
            + reflexivity.
        }

      (* EqTySubstBool *)
      - { destruct (eval_subst _ _ _ i) as (G' & ist_G' & D' & ist_D' & sbs' & ist_sbs').
          exists G'. split ; [ assumption | ..].
          exists (fun xs => bool). split.
          - apply (istran_TyCtxConv G) ; [ now capply CtxRefl | ..].
            apply (istran_Subst _ _ D D' _ (fun ys => bool) sbs sbs') ;
              [ .. | assumption].
            apply (istran_TyCtxConv D) ; [ now capply CtxRefl | ..].
            now constructor.
          - exists (fun xs => bool). split.
            + apply (istran_TyCtxConv G) ; [ now capply CtxRefl | ..].
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

(*
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
*)

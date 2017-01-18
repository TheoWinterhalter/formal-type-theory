(* Admissibile ptt rules. *)

Require Import syntax ptt myptt ptt_tactics.

(* Some preliminary lemmata *)
Lemma EqTyWeakNat :
  forall {G D A B sbs},
    issubst sbs G D ->
    istype D A ->
    istype D B ->
    isctx G ->
    isctx D ->
    eqtype (ctxextend G (Subst A sbs))
           (Subst (Subst B (sbweak D A)) (sbshift G A sbs))
           (Subst (Subst B sbs) (sbweak G (Subst A sbs))).
Proof.
  intros. gocompsubst. gocompsubst.
  Unshelve. assumption.
Defined.


Lemma compWeakZero :
  forall {G A B u},
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u B ->
    eqtype G A (Subst A (sbcomp (sbweak G B) (sbzero G B u))).
Proof.
  intros.
  eapply EqTySym ; try magic.
  eapply EqTyTrans ; [
    eapply CongTySubst ; [
      eapply WeakZero ; magic
    | magic ..
    ]
  | magic ..
  ].
Defined.

Lemma EqTyWeakZero :
  forall {G A B u},
    isctx G ->
    istype G A ->
    istype G B ->
    isterm G u B ->
    eqtype G A (Subst (Subst A (sbweak G B)) (sbzero G B u)).
Proof.
  intros.
  gocompsubst. eapply EqTySym ; try magic. apply compWeakZero ; magic.
Defined.

Lemma EqTyShiftZero :
  forall {G D A B v sbs},
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    isterm D v A ->
    isctx G ->
    isctx D ->
    eqtype
      G
      (Subst (Subst B (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
      (Subst (Subst B (sbzero D A v)) sbs).
Proof.
  intros. gocompsubst. gocompsubst.
  Unshelve. magic.
Defined.

Lemma EqTyCongZero :
  forall {G A1 A2 B1 B2 u1 u2},
    eqtype (ctxextend G A1) A2 B2 ->
    istype (ctxextend G A1) A2 ->
    istype (ctxextend G A1) B2 ->
    isctx G ->
    eqtype G A1 B1 ->
    eqterm G u1 u2 A1 ->
    istype G A1 ->
    istype G B1 ->
    isterm G u1 A1 ->
    isterm G u2 B1 ->
    eqtype G
           (Subst A2 (sbzero G A1 u1))
           (Subst B2 (sbzero G B1 u2)).
Proof.
  intros.
  assert (isterm G u2 A1).
  { eapply TermTyConv ; [
      eassumption
    | magic ..
    ].
  }
  eapply CongTySubst ; [
    magic ..
  | eapply SubstCtxConv ; magic
  ].
Defined.

Lemma EqTyCongShift :
  forall {G1 G2 D A1 A2 B1 B2 sbs1 sbs2},
    eqctx G1 G2 ->
    eqsubst sbs1 sbs2 G1 D ->
    eqtype D A1 A2 ->
    eqtype (ctxextend D A1) B1 B2 ->
    isctx G1 ->
    isctx G2 ->
    isctx D ->
    issubst sbs1 G1 D ->
    issubst sbs2 G2 D ->
    istype D A1 ->
    istype D A2 ->
    istype (ctxextend D A1) B1 ->
    istype (ctxextend D A2) B2 ->
    eqtype (ctxextend G1 (Subst A1 sbs1))
           (Subst B1 (sbshift G1 A1 sbs1))
           (Subst B2 (sbshift G2 A2 sbs2)).
Proof.
  intros.
  assert (issubst sbs2 G1 D).
  { eapply SubstCtxConv ; magic. }
  assert (issubst sbs1 G2 D).
  { eapply SubstCtxConv ; magic. }
  assert (istype (ctxextend D A1) B2).
  { eapply TyCtxConv ; [
      eassumption
    | magic ..
    ].
  }
  assert (eqsubst sbs2 sbs1 G2 D).
  { apply SubstSym ; try assumption.
    eapply EqSubstCtxConv ; magic.
  }
  eapply CongTySubst ; [
    magic ..
  | eapply SubstCtxConv ; magic
  ].
  Unshelve. all:assumption.
Defined.

Lemma EqTyCongWeak :
  forall {G1 G2 A1 A2 B1 B2},
    eqctx G1 G2 ->
    eqtype G1 A1 A2 ->
    eqtype G1 B1 B2 ->
    isctx G1 ->
    isctx G2 ->
    istype G1 A1 ->
    istype G1 B1 ->
    istype G2 A2 ->
    istype G2 B2 ->
    eqtype (ctxextend G1 A1)
           (Subst B1 (sbweak G1 A1))
           (Subst B2 (sbweak G2 A2)).
Proof.
  intros.
  assert (istype G1 A2).
  { eapply TyCtxConv ; [ eassumption | magic .. ]. }
  assert (istype G1 B2).
  { eapply TyCtxConv ; [ eassumption | magic .. ]. }
  eapply CongTySubst ; [
    magic ..
  | eapply SubstCtxConv ; magic
  ].
Defined.

Lemma EqSubstWeakNat :
  forall {G D A B u sbs},
    issubst sbs G D ->
    istype D A ->
    istype D B ->
    isterm D u B ->
    isctx G ->
    isctx D ->
    eqterm (ctxextend G (Subst A sbs))
           (subst (subst u (sbweak D A)) (sbshift G A sbs))
           (subst (subst u sbs) (sbweak G (Subst A sbs)))
           (Subst (Subst B sbs) (sbweak G (Subst A sbs))).
Proof.
  intros. eapply EqTyConv.
  - gocompsubst ; try eassumption ; try magic.
    + gocompsubst ; try eassumption ; try magic.
      * { eapply TermTyConv.
          - eapply TermSubst ; try magic.
            eapply TermSubst ; try magic.
            eassumption.
          - gocompsubst.
          - magic.
          - magic.
          - magic.
        }
      * { eapply TermTyConv.
          - eapply TermSubst ; try magic.
            eapply TermSubst ; try magic.
            eassumption.
          - gocompsubst.
          - magic.
          - magic.
          - magic.
        }
      * { eapply TermTyConv.
          - eapply TermSubst ; try magic.
            eassumption.
          - magic.
          - magic.
          - magic.
          - magic.
        }
      * gocompsubst.
      * { eapply TermTyConv.
          - eapply TermSubst ; try magic.
            eassumption.
          - gocompsubst.
          - magic.
          - magic.
          - magic.
        }
    + { eapply TermTyConv.
        - eapply TermSubst ; try magic.
          eapply TermSubst ; try magic.
          eassumption.
        - gocompsubst.
        - magic.
        - magic.
        - magic.
      }
    + { eapply TermTyConv.
        - eapply TermSubst ; try magic.
          eapply TermSubst ; try magic.
          eassumption.
        - gocompsubst.
        - magic.
        - magic.
        - magic.
      }
    + { eapply TermTyConv.
        - eapply TermSubst ; try magic.
          eapply TermSubst ; try magic.
          eassumption.
        - apply EqTySym ; try magic. apply EqTyWeakNat ; magic.
        - magic.
        - magic.
        - magic.
      }
  - apply EqTyWeakNat ; magic.
  - magic.
  - magic.
  - magic.
  - magic.
  - { eapply TermTyConv.
      - eapply TermSubst ; try magic.
        eapply TermSubst ; try magic.
        eassumption.
      - apply EqTySym ; try magic. apply EqTyWeakNat ; magic.
      - magic.
      - magic.
      - magic.
    }
  Unshelve. all:magic.
Defined.


Lemma EqSubstWeakZero :
  forall {G A B u v},
    istype G A ->
    istype G B ->
    isterm G u A ->
    isterm G v B ->
    isctx G ->
    eqterm G
           (subst (subst u (sbweak G B)) (sbzero G B v))
           u
           A.
Proof.
  intros.
  gocompsubst ; try eassumption ; try magic.
  - eapply EqTrans.
    + eapply CongTermSubst ; [
        eapply WeakZero ; magic
      | magic ..
      ].
    + apply EqIdSubst ; try magic.
      eapply TermTyConv ; [
        eassumption
      | try magic ..
      ].
      apply compWeakZero ; magic.
    + assumption.
    + magic.
    + magic.
    + eapply TermTyConv ; [
        eapply TermSubst ; try eassumption ; try magic
      | try magic ..
      ].
      apply EqTySym ; magic.
    + eapply TermTyConv ; [
        eassumption
      | try magic ..
      ].
      apply compWeakZero ; magic.
  - eapply TermTyConv ; [
      (eapply TermSubst ; try magic) ;
      (eapply TermSubst ; try magic) ;
      eassumption
    | try magic ..
    ].
    gocompsubst.
  - eapply TermTyConv ; [
      eassumption
    | try magic ..
    ].
    apply compWeakZero ; magic.
  - apply EqTySym ; try magic.
    apply EqTyWeakZero ; magic.
  - eapply TermTyConv ; [
      eassumption
    | try magic ..
    ].
    apply EqTyWeakZero ; magic.
  Unshelve. all:magic.
Defined.

Lemma EqTermShiftZero :
  forall {G D A B u v sbs},
    issubst sbs G D ->
    istype D A ->
    istype (ctxextend D A) B ->
    isterm (ctxextend D A) u B ->
    isterm D v A ->
    isctx G ->
    isctx D ->
    eqterm
      G
      (subst (subst u (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
      (subst (subst u (sbzero D A v)) sbs)
      (Subst (Subst B (sbzero D A v)) sbs).
Proof.
  intros.
  gocompsubst.
  - eapply TermTyConv ; [
      (eapply TermSubst ; try magic) ;
      (eapply TermSubst ; try magic) ;
      eassumption
    | try magic ..
    ].
    apply EqTyShiftZero ; magic.
  - gocompsubst.
    + eapply TermTyConv ; [
        (eapply TermSubst ; try magic) ;
        (eapply TermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
      gocompsubst.
    + eassumption.
    + eapply CongTermSubst ; [
        eapply ShiftZero ; magic
      | magic ..
      ].
    + eapply TermTyConv ; [
        (eapply TermSubst ; try magic) ;
        (eapply TermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
      gocompsubst.
    + eapply TermTyConv ; [
        (eapply TermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
    + eapply TermTyConv ; [
        (eapply TermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
    + gocompsubst.
    + eapply TermTyConv ; [
        (eapply TermSubst ; try magic) ;
        (eapply TermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
    + eapply TermTyConv ; [
        (eapply TermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
      gocompsubst.
  - eapply TermTyConv ; [
      (eapply TermSubst ; try magic) ;
      (eapply TermSubst ; try magic) ;
      eassumption
    | try magic ..
    ].
    gocompsubst.
  - eapply TermTyConv ; [
      (eapply TermSubst ; try magic) ;
      (eapply TermSubst ; try magic) ;
      eassumption
    | try magic ..
    ].
    gocompsubst.
  Unshelve. all:magic.
Defined.

Lemma EqTermCongWeak :
  forall {G1 G2 A1 A2 B1 B2 u1 u2},
    eqctx G1 G2 ->
    eqtype G1 A1 A2 ->
    eqtype G1 B1 B2 ->
    eqterm G1 u1 u2 B1 ->
    isctx G1 ->
    isctx G2 ->
    istype G1 A1 ->
    istype G1 B1 ->
    istype G2 B2 ->
    istype G2 A2 ->
    isterm G1 u1 B1 ->
    isterm G2 u2 B2 ->
    eqterm (ctxextend G1 A1)
           (subst u1 (sbweak G1 A1))
           (subst u2 (sbweak G2 A2))
           (Subst B1 (sbweak G1 A1)).
Proof.
  intros.
  assert (istype G1 A2).
  { eapply TyCtxConv ; [
      eassumption
    | magic ..
    ].
  }
  assert (istype G1 B2).
  { eapply TyCtxConv ; [
      eassumption
    | magic ..
    ].
  }
  assert (isterm G1 u2 B1).
  { eapply TermTyConv ; [
      eapply TermCtxConv ; [
        eassumption
      | magic ..
      ]
    | magic ..
    ].
  }
  eapply CongTermSubst ; [
    eapply CongSubstWeak ; magic
  | try magic ..
  ].
  eapply SubstCtxConv ; [
    eapply SubstWeak ; magic
  | magic ..
  ].
Defined.


(* Finally the lemma that we need to prove sanity of J. *)
Lemma JTyConv :
  forall {G D A C u v w p sbs},
    isctx G ->
    isctx D ->
    issubst sbs G D ->
    istype D A ->
    isterm D u A ->
    isterm D v A ->
    isterm D p (Id A u v) ->
    istype
      (ctxextend
         (ctxextend D A)
         (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
      )
      C ->
    isterm
      D
      w
      (Subst
         (Subst
            C
            (sbshift
               D
               (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
               (sbzero D A u))) (sbzero D (Id A u u) (refl A u))) ->
    isterm D v A ->
    isterm D p (Id A u v) ->
    eqtype
      G
      (Subst
         (Subst
            (Subst C
                   (sbshift
                      D
                      (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
                      (sbzero D A v)
                   )
            )
            (sbzero D (Id A u v) p)
         )
         sbs
      )
      (Subst
         (Subst
            (Subst C
                   (sbshift
                      (ctxextend G (Subst A sbs))
                      (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
                      (sbshift G A sbs)
                   )
            )
            (sbshift
               G
               (Id
                  (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
                  (subst (subst u sbs) (sbweak G (Subst A sbs)))
                  (var 0)
               )
               (sbzero G (Subst A sbs) (subst v sbs))
            )
         )
         (sbzero
            G
            (Id (Subst A sbs) (subst u sbs) (subst v sbs))
            (subst p sbs)
         )
      ).
Proof.
  intros.
  (* First let's have some assertions that we won't keep proving. *)
  assert (isterm D (refl A u) (Id A u u)).
  { now apply TermRefl. }
  assert (
    istype (ctxextend D A)
           (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
  ).
  { apply TyId ; magic. }
  assert (eqctx D D).
  { now apply CtxRefl. }
  assert (eqtype D (Subst (Subst A (sbweak D A)) (sbzero D A v)) A).
  { apply myEqTySym ; try magic.
    now apply EqTyWeakZero.
  }
  assert (isterm D u (Subst (Subst A (sbweak D A)) (sbzero D A v))).
  { eapply TermTyConv ; [ eassumption | magic .. ]. }
  assert (
    eqterm D
           (subst (subst u (sbweak D A)) (sbzero D A v)) u
           (Subst (Subst A (sbweak D A)) (sbzero D A v))
  ).
  { apply EqSubstWeakZero ; try assumption. magic. }
  assert (isterm D (subst (var 0) (sbzero D A v)) A).
  { eapply TermTyConv ; [
      eapply TermSubst ; magic
    | magic ..
    ].
  }
  assert (eqterm D (subst (var 0) (sbzero D A v)) v
    (Subst (Subst A (sbweak D A)) (sbzero D A v))).
  { eapply EqTyConv ; [
      eapply EqSubstZeroZero ; magic
    | magic ..
    ].
  }
  assert (isterm D v (Subst (Subst A (sbweak D A)) (sbzero D A v))).
  { eapply TermTyConv ; [ eassumption | magic .. ]. }
  assert (
    eqtype
      D
      (Id
         (Subst (Subst A (sbweak D A)) (sbzero D A v))
         (subst (subst u (sbweak D A)) (sbzero D A v))
         (subst (var 0) (sbzero D A v)))
      (Id A u v)
  ).
  { magic. }
  assert (
    eqtype D
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbzero D A v)) (Id A u v)
  ).
  { gopushsubst. }
  assert (
    eqctx
      (ctxextend
         D
         (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
                (sbzero D A v)))
      (ctxextend D (Id A u v))
  ).
  { magic. }
  assert (isctx (ctxextend D A)).
  { now apply CtxExtend. }
  assert (isctx
    (ctxextend (ctxextend D A)
       (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0)))).
  { now apply CtxExtend. }
  assert (isterm G (refl (Subst A sbs) (subst u sbs))
    (Id (Subst A sbs) (subst u sbs) (subst u sbs))).
  { apply TermRefl ; magic. }
  assert (
    isterm (ctxextend G (Subst A sbs)) (var 0)
    (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
  ).
  { apply TermVarZero ; magic. }
  assert (istype (ctxextend G (Subst A sbs))
    (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (subst (subst u sbs) (sbweak G (Subst A sbs))) (var 0))
  ).
  { apply TyId ; magic. }
  assert (eqctx G G).
  { apply CtxRefl. assumption. }
  assert (
    eqsubst
      (sbcomp
         sbs
         (sbcomp
            (sbweak G (Subst A sbs))
            (sbzero G (Subst A sbs) (subst v sbs)))
      )
      sbs
      G D
  ).
  { eapply SubstTrans ; [
      eapply CongSubstComp ; [
        eapply WeakZero ; magic
      | eapply SubstRefl ; magic
      | magic ..
      ]
    | magic ..
    ].
  }
  assert (eqtype D A A).
  { apply EqTyRefl ; assumption. }
  assert (eqtype G
    (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs))) (Subst A sbs)).
  { gocompsubst. gocompsubst.
    Unshelve. assumption.
  }
  assert (eqterm D u u A).
  { apply EqRefl ; assumption. }
  assert (
    eqsubst
      (sbcomp sbs
              (sbcomp (sbweak G (Subst A sbs))
                      (sbzero G (Subst A sbs) (subst v sbs))
              )
      )
      (sbcomp (sbweak D A) (sbcomp (sbzero D A v) sbs))
      G
      D
  ).
  { eapply SubstTrans ; [
      eapply CongSubstComp ; [
        eapply WeakZero ; magic
      | eapply SubstRefl ; magic
      | magic ..
      ]
    | try magic ..
    ].
    eapply mySubstSym ; try magic.
    eapply SubstTrans ; [
      eapply CompAssoc ; magic
    | try magic ..
    ].
    eapply SubstTrans ; [
      eapply CongSubstComp ; [
        eapply SubstRefl ; magic
      | eapply WeakZero ; magic
      | magic ..
      ]
    | try magic ..
    ].
    eapply SubstTrans ; [
      eapply CompIdLeft ; magic
    | magic ..
    ].
    Unshelve. assumption.
  }
  assert (
    eqtype G
           (Subst A
                  (sbcomp sbs
                          (sbcomp (sbweak G (Subst A sbs))
                                  (sbzero G (Subst A sbs) (subst v sbs))
                          )
                  )
           )
           (Subst A
                  (sbcomp (sbweak D A)
                          (sbcomp (sbzero D A v) sbs)
                  )
           )
  ).
  { eapply CongTySubst ; [ eassumption | magic .. ]. }
  assert (
    isterm G
           (subst u sbs)
           (Subst (Subst A sbs)
                  (sbcomp (sbweak G (Subst A sbs))
                          (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
    gocompsubst. gocompsubst. gocompsubst.
    Unshelve. assumption.
  }
  assert (
    isterm G
           (subst (subst (subst u sbs) (sbweak G (Subst A sbs)))
                  (sbzero G (Subst A sbs) (subst v sbs)))
           (Subst (Subst A sbs)
                  (sbcomp (sbweak G (Subst A sbs))
                          (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [
          magic
        | eapply TermSubst ; [ magic | eassumption | magic .. ]
        | magic ..
        ]
      | magic ..
      ]
    | try magic ..
    ].
    gocompsubst.
    Unshelve. all:assumption.
  }
  assert (
    eqsubst
      (sbcomp sbs
              (sbcomp
                 (sbcomp (sbweak G (Subst A sbs))
                         (sbzero G (Subst A sbs) (subst v sbs)))
                 (sbcomp (sbweak G (Subst A sbs))
                         (sbzero G (Subst A sbs) (subst v sbs)))))
      (sbcomp sbs
              (sbcomp (sbweak G (Subst A sbs))
                      (sbzero G (Subst A sbs) (subst v sbs))))
      G
      D
  ).
  { eapply CongSubstComp ; [
      eapply SubstTrans ; [
        eapply CongSubstComp ; [
          eapply WeakZero ; magic
        | eapply SubstRefl ; magic
        | magic ..
        ]
      | magic ..
      ]
    | eapply SubstRefl ; magic
    | magic ..
    ].
    Unshelve. assumption.
  }
  assert (
    eqtype G
           (Subst A
                  (sbcomp sbs
                          (sbcomp
                             (sbcomp (sbweak G (Subst A sbs))
                                     (sbzero G (Subst A sbs) (subst v sbs)))
                             (sbcomp (sbweak G (Subst A sbs))
                                     (sbzero G (Subst A sbs) (subst v sbs))))))
           (Subst A
                  (sbcomp sbs
                          (sbcomp (sbweak G (Subst A sbs))
                                  (sbzero G (Subst A sbs) (subst v sbs)))))
  ).
  { eapply CongTySubst ; [ eassumption | magic .. ]. }
  assert (
    isterm G
           (subst (subst u sbs)
                  (sbcomp (sbweak G (Subst A sbs))
                          (sbzero G (Subst A sbs) (subst v sbs))
                  )
           )
           (Subst A
                  (sbcomp sbs
                          (sbcomp (sbweak G (Subst A sbs))
                                  (sbzero G (Subst A sbs) (subst v sbs))
                          )
                  )
           )
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
    gocompsubst. gocompsubst.
    Unshelve. assumption.
  }
  assert (
    isterm G
           (subst u sbs)
           (Subst A
                  (sbcomp sbs
                          (sbcomp (sbweak G (Subst A sbs))
                                  (sbzero G (Subst A sbs) (subst v sbs)))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    eqterm G
    (subst (subst (subst u sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs))) (subst u sbs)
    (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { gocompsubst. gocompsubst.
    Unshelve. all:assumption.
  }
  assert (
    isterm G
           (subst (var 0) (sbzero G (Subst A sbs) (subst v sbs)))
           (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
    eassumption.
  }
  assert (
    eqterm G (subst (var 0) (sbzero G (Subst A sbs) (subst v sbs)))
    (subst v sbs)
    (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { eapply EqTyConv ; [
      eapply EqSubstZeroZero ; magic
    | eapply myEqTySym ; try magic ; eassumption
    | magic ..
    ].
  }
  assert (
    eqtype G (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) sbs)
    (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { gocompsubst. gocompsubst. gocompsubst. gocompsubst.
    Unshelve. assumption.
  }
  assert (
    isterm G (subst u sbs)
    (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    isterm G
           (subst v sbs)
           (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
                  (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype G
           (Subst
              (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
                  (subst (subst u sbs) (sbweak G (Subst A sbs)))
                  (var 0)) (sbzero G (Subst A sbs) (subst v sbs)))
           (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { gopushsubst. apply CongId ; try magic ; try assumption. }
  assert (
    eqctx
    (ctxextend G
       (Subst
          (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
             (subst (subst u sbs) (sbweak G (Subst A sbs)))
             (var 0)) (sbzero G (Subst A sbs) (subst v sbs))))
    (ctxextend G (Id (Subst A sbs) (subst u sbs) (subst v sbs)))
  ).
  { magic. }
  assert (isctx (ctxextend G (Subst A sbs))).
  { magic. }
  assert (
    eqtype (ctxextend G (Subst A sbs))
    (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
    (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
  ).
  { apply EqTyWeakNat ; assumption. }
  assert (
    eqtype (ctxextend G (Subst A sbs))
           (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) sbs)
                  (sbweak G (Subst A sbs)))
           (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
  ).
  { eapply EqTySym ; try magic.
    gocompsubst. gocompsubst.
    Unshelve. assumption.
  }
  assert (
    eqsubst
    (sbcomp (sbweak D A)
       (sbcomp (sbzero D A v) (sbcomp sbs (sbweak G (Subst A sbs)))))
    (sbcomp (sbweak D A)
       (sbcomp (sbzero D A v) (sbcomp (sbweak D A) (sbshift G A sbs))))
    (ctxextend G (Subst A sbs)) D
  ).
  { eapply CongSubstComp ; [
      eapply CongSubstComp ; [
        eapply mySubstSym ; magic
      | eapply SubstRefl ; magic
      | magic ..
      ]
    | eapply SubstRefl ; magic
    | magic ..
    ].
    Unshelve. assumption.
  }
  assert (
    eqtype (ctxextend G (Subst A sbs))
    (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) (sbweak D A))
       (sbshift G A sbs))
    (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) sbs)
       (sbweak G (Subst A sbs)))
  ).
  { gocompsubst. gocompsubst. gocompsubst. gocompsubst. gocompsubst.
    gocompsubst.
    Unshelve. assumption.
  }
  assert (
    isterm (ctxextend G (Subst A sbs))
    (subst (subst u (sbweak D A)) (sbshift G A sbs))
    (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) sbs)
       (sbweak G (Subst A sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [ magic | eassumption | magic .. ]
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqterm (ctxextend G (Subst A sbs))
    (subst (subst u (sbweak D A)) (sbshift G A sbs))
    (subst (subst u sbs) (sbweak G (Subst A sbs)))
    (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
  ).
  { eapply EqTyConv ; [
      eapply EqSubstWeakNat ; try magic ; eassumption
    | try magic ; try eassumption ..
    ].
    Unshelve. magic.
  }
  assert (
    eqtype (ctxextend G (Subst A sbs))
           (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
           (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
  ).
  { apply myEqTySym ; try magic. assumption. }
  assert (
    isterm (ctxextend G (Subst A sbs))
           (subst (var 0) (sbshift G A sbs))
           (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermVarZero ; magic
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (eqterm (ctxextend G (Subst A sbs)) (subst (var 0) (sbshift G A sbs))
    (var 0) (Subst (Subst A (sbweak D A)) (sbshift G A sbs))).
  { eapply EqTyConv ; [
      eapply EqSubstShiftZero ; magic
    | try magic ..
    ].
    assumption.
    Unshelve. assumption.
  }
  assert (
    isterm (ctxextend G (Subst A sbs))
    (subst (subst u sbs) (sbweak G (Subst A sbs)))
    (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [ magic | eassumption | magic .. ]
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    isterm (ctxextend G (Subst A sbs)) (var 0)
    (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermVarZero ; magic
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype (ctxextend G (Subst A sbs))
    (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (subst (subst u sbs) (sbweak G (Subst A sbs))) (var 0))
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbshift G A sbs))
  ).
  { gopushsubst. apply CongId ; try magic ; try assumption. }
  assert (
    eqctx
    (ctxextend (ctxextend G (Subst A sbs))
       (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
          (subst (subst u sbs) (sbweak G (Subst A sbs)))
          (var 0)))
    (ctxextend (ctxextend G (Subst A sbs))
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbshift G A sbs)))
  ).
  { magic.
    Unshelve. assumption.
  }
  assert (
    issubst
      (sbshift D
               (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
               (sbzero D A v))
      (ctxextend D (Id A u v))
      (ctxextend
         (ctxextend D A)
         (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0)))
  ).
  { eapply SubstCtxConv ; magic. }
  assert (istype D (Id A u v)).
  { magic. }
  assert (isctx (ctxextend G (Subst (Id A u v) sbs))).
  { magic. }
  assert (
    issubst (sbshift G (Id A u v) sbs) (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend D
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbzero D A v)))
  ).
  { eapply SubstCtxConv ; magic. }
  assert (
    eqsubst (sbcomp (sbweak D A) (sbcomp (sbzero D A v) sbs)) sbs G D
  ).
  { eapply SubstTrans ; [
      eapply CompAssoc ; magic
    | eapply SubstTrans ; [
        eapply CongSubstComp ; [
          eapply SubstRefl ; magic
        | eapply WeakZero ; magic
        | magic ..
        ]
      | magic ..
      ]
    | magic ..
    ].
    Unshelve. all:assumption.
  }
  assert (
    eqtype G (Subst A (sbcomp (sbweak D A) (sbcomp (sbzero D A v) sbs)))
    (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) (sbweak D A))
       (sbcomp (sbzero D A v) sbs))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    eqtype G
    (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) (sbweak D A))
       (sbcomp (sbzero D A v) sbs))
    (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v))
       (sbcomp (sbweak D A) (sbcomp (sbzero D A v) sbs)))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    isterm G
           (subst (subst u (sbweak D A)) (sbcomp (sbzero D A v) sbs))
           (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v))
                  (sbcomp (sbweak D A) (sbcomp (sbzero D A v) sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [ magic | eassumption | magic .. ]
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    isterm G (subst u sbs)
    (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v))
       (sbcomp (sbweak D A) (sbcomp (sbzero D A v) sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
    Unshelve. assumption.
  }
  assert (
    eqtype G (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) sbs)
    (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) (sbweak D A))
       (sbcomp (sbzero D A v) sbs))
  ).
  { gocompsubst. Unshelve. magic. }
  assert (
    isterm G (subst u sbs)
    (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) (sbweak D A))
       (sbcomp (sbzero D A v) sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype G
    (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) (sbweak D A))
       (sbcomp (sbzero D A v) sbs)) (Subst A sbs)
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    eqterm G (subst u sbs)
    (subst (subst u (sbweak D A)) (sbcomp (sbzero D A v) sbs))
    (Subst A sbs)
  ).
  { (* gocompsubst ; try eassumption ; try magic. *)

    eapply EqTyConv ; [
      eapply myEqSym ; [
        eapply eqterm_subst_left ; try magic ; try eassumption ; magic
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
    Unshelve. all:magic.
  }
  assert (
     eqtype G (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A v) sbs))
    (Subst A sbs)
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    isterm G (subst (var 0) (sbcomp (sbzero D A v) sbs)) (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermVarZero ; magic
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype G (Subst A sbs)
    (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A v) sbs))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    isterm G (subst (subst (var 0) (sbzero D A v)) sbs)
    (Subst (Subst A (sbweak D A)) (sbcomp (sbzero D A v) sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ eassumption | eassumption | magic .. ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqterm G
           (subst v sbs)
           (subst (var 0) (sbcomp (sbzero D A v) sbs))
           (Subst A sbs)
  ).
  { eapply myEqSym ; try magic.
    eapply EqTrans ; [
      eapply EqTyConv ; [
        eapply myEqSym ; [
          eapply EqSubstComp ; [
            shelve
          | eassumption
          | magic ..
          ]
        | magic ..
        ]
      | try magic ; assumption ..
      ]
    | magic ..
    ].
    Unshelve. all:magic.
  }
  assert (
     isterm G (subst (subst u (sbweak D A)) (sbcomp (sbzero D A v) sbs))
    (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [ magic | eassumption | magic .. ]
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype G
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp (sbzero D A v) sbs)) (Subst (Id A u v) sbs)
  ).
  { gopushsubst. gopushsubst. eapply CongId ; try magic ; try assumption. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbcomp (sbzero D A v) sbs))) (ctxextend G (Subst (Id A u v) sbs))
  ).
  { eapply EqCtxExtend ; try magic. assumption. }
  assert (
    eqsubst
    (sbcomp
       (sbweak D A)
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    sbs
    G D
  ).
  { eapply SubstTrans ; [
      eapply CongSubstComp ; [
        eapply ShiftZero ; magic
      | eapply SubstRefl ; magic
      | magic ..
      ]
    | magic ..
    ].
    Unshelve. all:assumption.
  }
  assert (
    eqtype G
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (Subst A sbs)
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    eqtype G
    (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (Subst A
       (sbcomp (sbweak D A)
          (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs)))))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    isterm G
    (subst (subst u (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (Subst A
       (sbcomp (sbweak D A)
          (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs)))))
  ).
  { eapply TermTyConv ; [
      (eapply TermSubst ; try magic) ;
      (eapply TermSubst ; try magic) ;
      eassumption
    | try magic ..
    ].
    assumption.
    Unshelve. all:magic.
  }
  assert (
    isterm G (subst u sbs)
    (Subst A
       (sbcomp (sbweak D A)
          (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs)))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
    Unshelve. assumption.
  }
  assert (
    eqterm G
    (subst (subst u (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (subst u sbs)
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    isterm (ctxextend D A) (var 0) (Subst A (sbweak D A))
  ).
  { magic. }
  assert (
    eqtype G
    (Subst (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs)))
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    isterm G
    (subst (subst (var 0) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs)))
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
       | eapply TermSubst ; [
           magic
         | eapply TermVarZero ; magic
         | magic ..
        ]
       | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype G (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) sbs)
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    isterm G (subst v sbs)
   (Subst (Subst A (sbweak D A))
      (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eassumption
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqsubst
      (sbcomp (sbweak D A)
              (sbcomp (sbshift G A sbs)
                      (sbzero G (Subst A sbs) (subst v sbs))))
      (sbcomp sbs
              (sbcomp (sbweak G (Subst A sbs))
                      (sbzero G (Subst A sbs) (subst v sbs))))
      G
      D
  ).
  { eapply SubstTrans ; [
      eapply CompAssoc ; magic
    | try magic ..
    ].
    eapply SubstTrans ; [
      eapply CongSubstComp ; [
        eapply SubstRefl ; magic
      | eapply WeakNat ; magic
      | magic ..
      ]
    | try magic ..
    ].
    eapply mySubstSym ; try magic.
    eapply SubstTrans ; [
      eapply CompAssoc ; magic
    | magic ..
    ].
    Unshelve. magic.
  }
  assert (
     eqtype G
    (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs)))
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { gocompsubst. gocompsubst. gocompsubst.
    Unshelve. assumption.
  }
  assert (
    isterm G (subst (var 0) (sbzero G (Subst A sbs) (subst v sbs)))
   (Subst (Subst A (sbweak D A))
      (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermVarZero ; magic
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype G (Subst A sbs)
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    eqterm G
    (subst (var 0)
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (subst v sbs)
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { eapply EqTrans ; [
      eapply myEqSym ; [
        eapply EqSubstComp ; [ shelve | magic .. ]
      | magic ..
      ]
    | try magic ..
    ].
    eapply EqTrans ; [
      eapply EqTyConv ; [
        eapply CongTermSubst ; [
          eapply SubstRefl ; magic
        | eapply EqSubstShiftZero ; magic
        | magic ..
        ]
      | try magic ; assumption ..
      ]
    | try magic ..
    ].
    eapply EqTyConv ; [
      eapply EqSubstZeroZero ; magic
    | try magic ..
    ].
    assumption.
    Unshelve. all:magic.
  }
  assert (
    isterm G (subst u sbs)
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype G
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (Subst (Id A u v) sbs)
  ).
  { gopushsubst. gopushsubst. apply myEqTySym ; try magic.
    eapply CongId ; try magic ; assumption.
  }
  assert (
    eqctx
    (ctxextend G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs)))))
    (ctxextend G (Subst (Id A u v) sbs))
  ).
  { apply EqCtxExtend ; try magic. assumption. }
  assert (istype G (Id (Subst A sbs) (subst u sbs) (subst v sbs))).
  { magic. }
  assert (
    eqtype G (Id (Subst A sbs) (subst u sbs) (subst v sbs))
    (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { apply EqTyRefl ; assumption. }
  assert (
     eqtype G
            (Subst (Id A u v) sbs)
            (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { gopushsubst. }
  assert (
    isterm G (subst p sbs) (Id (Subst A sbs) (subst u sbs) (subst v sbs))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | magic ..
    ].
  }
  assert (
    eqtype G
    (Subst
       (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) (sbweak D A))
          (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
    (Subst A sbs)
  ).
  { gocompsubst. gocompsubst. Unshelve. assumption. }
  assert (
    isterm G
    (subst (subst (subst u (sbweak D A)) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs))) (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [
          magic
        | eapply TermSubst ; [ magic | eassumption | magic .. ]
        | magic ..
        ]
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype G
    (Subst (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs))) (Subst A sbs)
  ).
  { gocompsubst. gocompsubst. Unshelve. assumption. }
  assert (
    isterm G
    (subst (subst (var 0) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs))) (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [ magic | eassumption | magic .. ]
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype G (Subst A sbs)
    (Subst (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { gocompsubst. gocompsubst. Unshelve. assumption. }
  assert (
    eqtype G
    (Subst
       (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) (sbweak D A))
          (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    isterm G
    (subst (subst (subst u (sbweak D A)) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs)))
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [
          magic
        | eapply TermSubst ; [ magic | eassumption | magic .. ]
        | magic ..
        ]
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqsubst
    (sbcomp (sbweak D A)
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (sbcomp (sbweak D A) (sbcomp (sbzero D A v) sbs)) G D
  ).
  { eapply CongSubstComp ; magic. }
  assert (
    eqtype G (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) sbs)
    (Subst (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { gocompsubst. gocompsubst. gocompsubst. gocompsubst.
    Unshelve. assumption.
  }
  assert (
    isterm G (subst u sbs)
    (Subst (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqterm G (subst u sbs)
    (subst (subst (subst u (sbweak D A)) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs))) (Subst A sbs)
  ).
  { gocompsubst ; try eassumption ; magic.
    Unshelve. all:magic.
  }
  assert (
    isterm G (subst v sbs)
    (Subst (Subst (Subst A (sbweak D A)) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [ magic | eassumption | magic .. ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqterm G (subst v sbs)
    (subst (subst (var 0) (sbshift G A sbs))
       (sbzero G (Subst A sbs) (subst v sbs))) (Subst A sbs)
  ).
  { eapply myEqSym ; try magic.
    gocompsubst ; assumption.
  }
  assert (
    eqtype G
    (Subst
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
    (Subst (Id A u v) sbs)
  ).
  { gopushsubst. gopushsubst. gopushsubst.
    apply CongId ; try magic ; assumption.
    Unshelve. assumption.
  }
  assert (
    eqctx
    (ctxextend G
       (Subst
          (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
             (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs))))
    (ctxextend G (Subst (Id A u v) sbs))
  ).
  { apply EqCtxExtend ; try magic. assumption. }
  assert (
    isctx
    (ctxextend (ctxextend G (Subst A sbs))
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbshift G A sbs)))
  ).
  { apply CtxExtend.
    - assumption.
    - magic.
  }
  assert (
    istype G
   (Subst
      (Subst
         (Subst C
            (sbshift (ctxextend G (Subst A sbs))
               (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
               (sbshift G A sbs)))
         (sbshift G
            (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
               (subst (subst u sbs) (sbweak G (Subst A sbs)))
               (var 0)) (sbzero G (Subst A sbs) (subst v sbs))))
      (sbzero G (Id (Subst A sbs) (subst u sbs) (subst v sbs)) (subst p sbs)))
  ).
  { eapply TySubst ; try magic.
    eapply TySubst ; try magic.
    eapply SubstCtxConv ; magic.
    Unshelve. assumption.
  }
  assert (
    issubst
    (sbshift G
       (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
          (subst (subst u sbs) (sbweak G (Subst A sbs)))
          (var 0)) (sbzero G (Subst A sbs) (subst v sbs)))
    (ctxextend G (Id (Subst A sbs) (subst u sbs) (subst v sbs)))
    (ctxextend (ctxextend G (Subst A sbs))
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbshift G A sbs)))
  ).
  { eapply SubstCtxConv ; magic.
    Unshelve. assumption.
  }
  assert (
    issubst
    (sbshift G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbzero D A v)) sbs) (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend D (Id A u v))
  ).
  { eapply SubstCtxConv ; magic.
    Unshelve. assumption.
  }
  assert (
    eqtype G
    (Subst
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbzero D A v)) sbs)
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp (sbzero D A v) sbs))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    eqctx
    (ctxextend G
       (Subst
          (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
             (sbzero D A v)) sbs))
    (ctxextend G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbcomp (sbzero D A v) sbs)))
  ).
  { eapply EqCtxExtend ; try magic. assumption. }
  assert (
    issubst
   (sbcomp
      (sbshift D (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
         (sbzero D A v))
      (sbshift G
         (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
            (sbzero D A v)) sbs))
   (ctxextend G
      (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
         (sbcomp (sbzero D A v) sbs)))
   (ctxextend (ctxextend D A)
      (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0)))
  ).
  { eapply SubstCtxConv ; try magic. assumption. }
  assert (
    issubst
    (sbshift G (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp (sbzero D A v) sbs)) (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend (ctxextend D A)
       (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0)))
  ).
  { eapply SubstCtxConv ; try magic. assumption. }
  assert (
    issubst
    (sbshift G (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (ctxextend G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbcomp (sbzero D A v) sbs)))
    (ctxextend (ctxextend D A)
       (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0)))
  ).
  { eapply SubstCtxConv ; magic. }
  assert (
    issubst
    (sbshift G (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend (ctxextend D A)
       (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0)))
  ).
  { eapply SubstCtxConv ; try magic. assumption. }
  assert (
    eqtype G
    (Subst
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { gocompsubst. Unshelve. assumption. }
  assert (
    eqctx
    (ctxextend G
       (Subst
          (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
             (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs))))
    (ctxextend G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs)))))
  ).
  { eapply EqCtxExtend ; try magic. assumption. }
  assert (
    issubst
   (sbcomp
      (sbshift (ctxextend G (Subst A sbs))
         (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
         (sbshift G A sbs))
      (sbshift G
         (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
            (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs))))
   (ctxextend G
      (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
         (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs)))))
   (ctxextend (ctxextend D A)
      (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0)))
  ).
  { eapply SubstCtxConv ; try magic. assumption. }
  assert (
    issubst
    (sbcomp
       (sbshift (ctxextend G (Subst A sbs))
          (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbshift G A sbs))
       (sbshift G
          (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
             (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs))))
    (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend (ctxextend D A)
       (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0)))
  ).
  { eapply SubstCtxConv ; try magic. assumption. }
  assert (
    issubst
    (sbshift G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
    (ctxextend G (Subst (Id A u v) sbs))
    (ctxextend (ctxextend G (Subst A sbs))
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbshift G A sbs)))
  ).
  { eapply SubstCtxConv ; try magic. assumption.
    Unshelve. all:assumption.
  }
  assert (
    issubst
   (sbshift G
      (Id (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
         (subst (subst u sbs) (sbweak G (Subst A sbs)))
         (var 0)) (sbzero G (Subst A sbs) (subst v sbs)))
   (ctxextend G
      (Subst
         (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
            (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs))))
   (ctxextend (ctxextend G (Subst A sbs))
      (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
         (sbshift G A sbs)))
  ).
  { eapply SubstCtxConv ; magic.
    Unshelve. all:assumption.
  }
  assert (
    issubst
      (sbzero G
              (Id (Subst A sbs) (subst u sbs) (subst v sbs))
              (subst p sbs)
      )
      G
      (ctxextend G (Subst (Id A u v) sbs))
  ).
  { eapply SubstCtxConv ; magic. }
  assert (
    eqtype G
    (Subst
       (Subst (Subst (Subst (Subst A (sbweak D A)) (sbzero D A v)) sbs)
          (sbweak G (Subst A sbs))) (sbzero G (Subst A sbs) (subst v sbs)))
    (Subst A sbs)
  ).
  { gocompsubst. gocompsubst. Unshelve. assumption. }
  assert (
    isterm G
    (subst (subst (subst u sbs) (sbweak G (Subst A sbs)))
       (sbzero G (Subst A sbs) (subst v sbs))) (Subst A sbs)
  ).
  { eapply TermTyConv ; [
      eapply TermSubst ; [
        magic
      | eapply TermSubst ; [
          magic
        | eapply TermSubst ; [ magic | eassumption | magic .. ]
        | magic ..
        ]
      | magic ..
      ]
    | try magic ..
    ].
    assumption.
  }
  assert (
    eqtype G (Subst A sbs)
   (Subst (Subst (Subst A sbs) (sbweak G (Subst A sbs)))
      (sbzero G (Subst A sbs) (subst v sbs)))
  ).
  { gocompsubst. gocompsubst. Unshelve. assumption. }
  assert (
     eqterm G (subst u sbs)
   (subst (subst (subst u sbs) (sbweak G (Subst A sbs)))
      (sbzero G (Subst A sbs) (subst v sbs))) (Subst A sbs)
  ).
  { eapply myEqSym ; try magic. eapply EqSubstWeakZero ; magic. }
  assert (
     eqterm G
            (subst v sbs)
            (subst (var 0) (sbzero G (Subst A sbs) (subst v sbs)))
            (Subst A sbs)
  ).
  { eapply myEqSym ; try magic. eapply EqSubstZeroZero ; magic. }
  (* Now let's proceed with the proof. *)
  (* We start by composing all the substitutions so we can forget about
     the types. *)
  gocompsubst ; try assumption.
  gocompsubst ; try assumption.
  gocompsubst ; try assumption.
  gocompsubst ; try assumption.
  (* Now we can focus on susbtitutions. *)
  eapply CongTySubst ; try magic.
  (* We go from the rhs. *)
  eapply mySubstSym ; try magic.
  eapply SubstTrans ; [
    (* Then we only look on the lhs of the composition. *)
    eapply CongSubstComp ; [
      (* We exchange the substitutionss. *)
      eapply mySubstSym ; [
        eapply ShiftZero ; magic
      | magic ..
      ]
    | (* We don't touch the rhs. *)
      eapply SubstRefl ; magic
    | magic ..
    ]
  | try magic ..
  ].
  (* We're using associativity to look at the rhs. *)
  eapply SubstTrans ; [
    eapply CompAssoc ; magic
  | try magic ..
  ].
  (* We can now have a look at the rhs of the composition. *)
  eapply SubstTrans ; [
    eapply CongSubstComp ; [
      (* On the left we remain unchanged. *)
      eapply SubstRefl ; magic
    | (* On the right we have a composition of shifts, thus we use
         fonctoriality to progress.
         However we need to apply congruence again to rewrite
         the type in the left shift. *)
      eapply CongSubstComp ; [
        eapply @CongSubstShift
        with (A2 := Subst
                     (Id (Subst A (sbweak D A))
                         (subst u (sbweak D A))
                         (var 0))
                     (sbzero D A v)
             ) ; try magic ;
        (apply CtxRefl ; magic)
      | (* We don't change the other substitution. *)
        apply SubstRefl ; magic
      | magic ..
      ]
    | magic ..
    ]
  | try magic ..
  ].
  (* Now that we rewrote the type, we can use fonctoriality. *)
  (* Note this could be meged with the next couple steps. *)
  eapply SubstTrans ; [
    eapply CongSubstComp ; [
      (* On the left we remain unchanged. *)
      eapply SubstRefl ; magic
    | eapply EqSubstCtxConv ; [
        eapply CompShift ; magic
      | try magic ; assumption ..
      ]
    | magic ..
    ]
  | try magic ..
  ].
  (* Now that we have a composition inside the shift, we want
     to proceed with an exchange by using ShiftZero. *)
  eapply SubstTrans ; [
    eapply CongSubstComp ; [
      (* We leave the left unchanged. *)
      eapply SubstRefl ; magic
    | eapply EqSubstCtxConv ; [
        eapply CongSubstShift ; [
          eassumption
        | eapply mySubstSym ; [
            eapply ShiftZero ; magic
          | magic ..
          ]
        | magic ..
        ]
      | try magic ; assumption ..
      ]
    | magic ..
    ]
  | try magic ..
  ].
  (* Now we need to apply CompShift again to put the composition outside
     and apply associativity. *)
  eapply SubstTrans ; [
    eapply CongSubstComp ; [
      (* On the left we remain unchanged. *)
      eapply SubstRefl ; magic
    | eapply mySubstSym ; [
        eapply EqSubstCtxConv ; [
          eapply CompShift ; magic
        | try magic ; assumption ..
        ]
      | magic ..
      ]
    | magic ..
    ]
  | try magic ..
  ].
  (* Now, it's time to apply associativity guys. *)
  eapply SubstTrans ; [
    eapply mySubstSym ; [
      eapply CompAssoc ; magic
    | magic ..
    ]
  | try magic ..
  ].
  (* Now we should finally have the same structure for the substitutions
     and thus be able to apply congruences. *)
  eapply CongSubstComp ; try magic.
  eapply CongSubstComp ; try magic ; try assumption.
  - eapply EqSubstCtxConv ; [
      eapply CongSubstShift ; magic
    | try magic ; assumption ..
    ].
  - eapply SubstCtxConv ; try magic.
    eapply EqCtxExtend ; try magic.
    gopushsubst. gopushsubst. eapply CongId ; try magic ; try assumption.
  Unshelve. all:assumption.
Defined.

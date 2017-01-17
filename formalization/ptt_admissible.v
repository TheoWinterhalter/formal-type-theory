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
  eapply myEqTyTrans ; [
    eapply myCongTySubst ; [
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
  { eapply myTermTyConv ; [
      eassumption
    | magic ..
    ].
  }
  eapply myCongTySubst ; [
    magic ..
  | eapply mySubstCtxConv ; magic
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
  { eapply mySubstCtxConv ; magic. }
  assert (issubst sbs1 G2 D).
  { eapply mySubstCtxConv ; magic. }
  assert (istype (ctxextend D A1) B2).
  { eapply myTyCtxConv ; [
      eassumption
    | magic ..
    ].
  }
  assert (eqsubst sbs2 sbs1 G2 D).
  { apply SubstSym ; try assumption.
    eapply myEqSubstCtxConv ; magic.
  }
  eapply myCongTySubst ; [
    magic ..
  | eapply mySubstCtxConv ; magic
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
  { eapply myTyCtxConv ; [ eassumption | magic .. ]. }
  assert (istype G1 B2).
  { eapply myTyCtxConv ; [ eassumption | magic .. ]. }
  eapply myCongTySubst ; [
    magic ..
  | eapply mySubstCtxConv ; magic
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
  intros. eapply myEqTyConv.
  - gocompsubst ; try eassumption ; try magic.
    + gocompsubst ; try eassumption ; try magic.
      * { eapply myTermTyConv.
          - eapply myTermSubst ; try magic.
            eapply myTermSubst ; try magic.
            eassumption.
          - gocompsubst.
          - magic.
          - magic.
          - magic.
        }
      * { eapply myTermTyConv.
          - eapply myTermSubst ; try magic.
            eapply myTermSubst ; try magic.
            eassumption.
          - gocompsubst.
          - magic.
          - magic.
          - magic.
        }
      * { eapply myTermTyConv.
          - eapply myTermSubst ; try magic.
            eassumption.
          - magic.
          - magic.
          - magic.
          - magic.
        }
      * gocompsubst.
      * { eapply myTermTyConv.
          - eapply myTermSubst ; try magic.
            eassumption.
          - gocompsubst.
          - magic.
          - magic.
          - magic.
        }
    + { eapply myTermTyConv.
        - eapply myTermSubst ; try magic.
          eapply myTermSubst ; try magic.
          eassumption.
        - gocompsubst.
        - magic.
        - magic.
        - magic.
      }
    + { eapply myTermTyConv.
        - eapply myTermSubst ; try magic.
          eapply myTermSubst ; try magic.
          eassumption.
        - gocompsubst.
        - magic.
        - magic.
        - magic.
      }
    + { eapply myTermTyConv.
        - eapply myTermSubst ; try magic.
          eapply myTermSubst ; try magic.
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
  - { eapply myTermTyConv.
      - eapply myTermSubst ; try magic.
        eapply myTermSubst ; try magic.
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
  - eapply myEqTrans.
    + eapply myCongTermSubst ; [
        eapply WeakZero ; magic
      | magic ..
      ].
    + apply EqIdSubst ; try magic.
      eapply myTermTyConv ; [
        eassumption
      | try magic ..
      ].
      apply compWeakZero ; magic.
    + assumption.
    + magic.
    + magic.
    + eapply myTermTyConv ; [
        eapply myTermSubst ; try eassumption ; try magic
      | try magic ..
      ].
      apply EqTySym ; magic.
    + eapply myTermTyConv ; [
        eassumption
      | try magic ..
      ].
      apply compWeakZero ; magic.
  - eapply myTermTyConv ; [
      (eapply myTermSubst ; try magic) ;
      (eapply myTermSubst ; try magic) ;
      eassumption
    | try magic ..
    ].
    gocompsubst.
  - eapply myTermTyConv ; [
      eassumption
    | try magic ..
    ].
    apply compWeakZero ; magic.
  - apply EqTySym ; try magic.
    apply EqTyWeakZero ; magic.
  - eapply myTermTyConv ; [
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
  - eapply myTermTyConv ; [
      (eapply myTermSubst ; try magic) ;
      (eapply myTermSubst ; try magic) ;
      eassumption
    | try magic ..
    ].
    apply EqTyShiftZero ; magic.
  - gocompsubst.
    + eapply myTermTyConv ; [
        (eapply myTermSubst ; try magic) ;
        (eapply myTermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
      gocompsubst.
    + eassumption.
    + eapply myCongTermSubst ; [
        eapply ShiftZero ; magic
      | magic ..
      ].
    + eapply myTermTyConv ; [
        (eapply myTermSubst ; try magic) ;
        (eapply myTermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
      gocompsubst.
    + eapply myTermTyConv ; [
        (eapply myTermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
    + eapply myTermTyConv ; [
        (eapply myTermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
    + gocompsubst.
    + eapply myTermTyConv ; [
        (eapply myTermSubst ; try magic) ;
        (eapply myTermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
    + eapply myTermTyConv ; [
        (eapply myTermSubst ; try magic) ;
        eassumption
      | try magic ..
      ].
      gocompsubst.
  - eapply myTermTyConv ; [
      (eapply myTermSubst ; try magic) ;
      (eapply myTermSubst ; try magic) ;
      eassumption
    | try magic ..
    ].
    gocompsubst.
  - eapply myTermTyConv ; [
      (eapply myTermSubst ; try magic) ;
      (eapply myTermSubst ; try magic) ;
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
  { eapply myTyCtxConv ; [
      eassumption
    | magic ..
    ].
  }
  assert (istype G1 B2).
  { eapply myTyCtxConv ; [
      eassumption
    | magic ..
    ].
  }
  assert (isterm G1 u2 B1).
  { eapply myTermTyConv ; [
      eapply myTermCtxConv ; [
        eassumption
      | magic ..
      ]
    | magic ..
    ].
  }
  eapply myCongTermSubst ; [
    eapply CongSubstWeak ; magic
  | try magic ..
  ].
  eapply mySubstCtxConv ; [
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
  { eapply myTermTyConv ; [ eassumption | magic .. ]. }
  assert (
    eqterm D
           (subst (subst u (sbweak D A)) (sbzero D A v)) u
           (Subst (Subst A (sbweak D A)) (sbzero D A v))
  ).
  { apply EqSubstWeakZero ; try assumption. magic. }
  assert (isterm D (subst (var 0) (sbzero D A v)) A).
  { eapply myTermTyConv ; [
      eapply myTermSubst ; magic
    | magic ..
    ].
  }
  assert (eqterm D (subst (var 0) (sbzero D A v)) v
    (Subst (Subst A (sbweak D A)) (sbzero D A v))).
  { eapply myEqTyConv ; [
      eapply EqSubstZeroZero ; magic
    | magic ..
    ].
  }
  assert (isterm D v (Subst (Subst A (sbweak D A)) (sbzero D A v))).
  { eapply myTermTyConv ; [ eassumption | magic .. ]. }
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
  { eapply mySubstTrans ; [
      eapply myCongSubstComp ; [
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
  { eapply mySubstTrans ; [
      eapply myCongSubstComp ; [
        eapply WeakZero ; magic
      | eapply SubstRefl ; magic
      | magic ..
      ]
    | try magic ..
    ].
    eapply mySubstSym ; try magic.
    eapply mySubstTrans ; [
      eapply myCompAssoc ; magic
    | try magic ..
    ].
    eapply mySubstTrans ; [
      eapply myCongSubstComp ; [
        eapply SubstRefl ; magic
      | eapply WeakZero ; magic
      | magic ..
      ]
    | try magic ..
    ].
    eapply mySubstTrans ; [
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
  { eapply myCongTySubst ; [ eassumption | magic .. ]. }
  assert (
    isterm G
           (subst u sbs)
           (Subst (Subst A sbs)
                  (sbcomp (sbweak G (Subst A sbs))
                          (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [
        magic
      | eapply myTermSubst ; [
          magic
        | eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  { eapply myCongSubstComp ; [
      eapply mySubstTrans ; [
        eapply myCongSubstComp ; [
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
  { eapply myCongTySubst ; [ eassumption | magic .. ]. }
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  { eapply myEqTyConv ; [
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  (* { eapply myCongSubstComp. *)
  { admit. }
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [
        magic
      | eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  { eapply myEqTyConv ; [
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [
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
  { eapply myEqTyConv ; [
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [
        magic
      | eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  { eapply myTermTyConv ; [
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
  { eapply mySubstCtxConv ; magic. }
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
  { eapply mySubstCtxConv ; magic. }
  assert (
    eqsubst (sbcomp (sbweak D A) (sbcomp (sbzero D A v) sbs)) sbs G D
  ).
  { eapply mySubstTrans ; [
      eapply myCompAssoc ; magic
    | eapply mySubstTrans ; [
        eapply myCongSubstComp ; [
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [
        magic
      | eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [ magic | eassumption | magic .. ]
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
  { eapply myTermTyConv ; [
      eapply myTermSubst ; [ magic | eassumption | magic .. ]
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

    eapply myEqTyConv ; [
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
    eqterm G
           (subst v sbs)
           (subst (var 0) (sbcomp (sbzero D A v) sbs))
           (Subst A sbs)
  ).
  (* { apply EqSym. eapply EqTrans. *)
  (*   { eapply EqTyConv. *)
  (*     - eapply EqSym. eapply EqSubstComp. *)
  (*       + shelve. *)
  (*       + eassumption. *)
  (*       + magic. *)
  (*       Unshelve. Focus 2. apply TermVarZero. assumption. *)
  (*     - gocompsubst. eapply CongTySubst. *)
  (*       + eapply SubstTrans. *)
  (*         { eapply CompAssoc ; magic. } *)
  (*         eapply SubstTrans. *)
  (*         { eapply CongSubstComp. *)
  (*           - eapply SubstRefl. eassumption. *)
  (*           - eapply WeakZero. assumption. *)
  (*         } *)
  (*         eapply CompIdLeft. assumption. *)
  (*       + assumption. *)
  (*   } *)
  (*   eapply CongTermSubst. *)
  (*   - eapply SubstRefl. eassumption. *)
  (*   - eapply EqSubstZeroZero. assumption. *)
  (* } *)
  { admit. }
  assert (
    eqtype G
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp (sbzero D A v) sbs)) (Subst (Id A u v) sbs)
  ).
  (* { gopushsubst. gopushsubst. apply CongId. *)
  (*   - gocompsubst. eapply CongTySubst ; eassumption. *)
  (*   - assumption. *)
  (*   - assumption. *)
  (* } *)
  { admit. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbcomp (sbzero D A v) sbs))) (ctxextend G (Subst (Id A u v) sbs))
  ).
  (* { apply EqCtxExtend. *)
  (*   - assumption. *)
  (*   - assumption. *)
  (* } *)
  { admit. }
  assert (
    eqsubst
    (sbcomp
       (sbweak D A)
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    sbs
    G D
  ).
  (* { eapply SubstTrans. *)
  (*   { eapply CongSubstComp. *)
  (*     eapply ShiftZero ; eassumption. *)
  (*     - eapply SubstRefl. magic. *)
  (*   } *)
  (*   eapply SubstTrans. *)
  (*   { eapply CompAssoc ; magic. } *)
  (*   eapply SubstTrans. *)
  (*   { eapply CongSubstComp. *)
  (*     - eapply SubstRefl. magic. *)
  (*     - eapply WeakZero. assumption. *)
  (*   } *)
  (*   eapply CompIdLeft. assumption. *)
  (* } *)
  { admit. }
  assert (
    eqtype G
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (Subst A sbs)
  ).
  { gocompsubst. }
  assert (
    eqterm G
    (subst (subst u (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (subst u sbs)
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  (* { gocompsubst. eapply CongTermSubst ; eassumption. } *)
  { admit. }
  assert (
    isterm (ctxextend D A) (var 0) (Subst A (sbweak D A))
  ).
  (* { apply TermVarZero. assumption. } *)
  { admit. }
  assert (
    eqterm G
    (subst (var 0)
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (subst v sbs)
    (Subst (Subst A (sbweak D A))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
  ).
  (* { eapply EqTrans. *)
  (*   { eapply EqSym. eapply EqSubstComp ; magic. } *)
  (*   eapply EqTrans. *)
  (*   { eapply EqTyConv. *)
  (*     - eapply CongTermSubst. *)
  (*       + eapply SubstRefl. magic. *)
  (*       + eapply EqSubstShiftZero ; eassumption. *)
  (*     - gocompsubst. gocompsubst. gocompsubst. *)
  (*       eapply CongTySubst. *)
  (*       + eapply SubstTrans. eassumption. *)
  (*         apply SubstSym. assumption. *)
  (*       + assumption. *)
  (*   } *)
  (*   eapply EqTyConv. *)
  (*   - eapply EqSubstZeroZero. magic. *)
  (*   - apply EqTySym. assumption. *)
  (* } *)
  { admit. }
  assert (
    eqtype G
    (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
       (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs))))
    (Subst (Id A u v) sbs)
  ).
  (* { gopushsubst. gopushsubst. apply EqTySym. apply CongId ; assumption. } *)
  { admit. }
  assert (
    eqctx
    (ctxextend G
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbcomp (sbshift G A sbs) (sbzero G (Subst A sbs) (subst v sbs)))))
    (ctxextend G (Subst (Id A u v) sbs))
  ).
  (* { now apply EqCtxExtend. } *)
  { admit. }
  assert (istype G (Id (Subst A sbs) (subst u sbs) (subst v sbs))).
  { apply TyId ; magic. }
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
  (* { eapply TermTyConv. *)
  (*   - eapply TermSubst. *)
  (*     * eassumption. *)
  (*     * eassumption. *)
  (*   - assumption. *)
  (* } *)
  { admit. }
  assert (
    eqtype G
    (Subst
       (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
          (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs)))
    (Subst (Id A u v) sbs)
  ).
  (* { gopushsubst. *)
  (*   - eapply CongId ; eassumption. *)
  (*   - gopushsubst. gopushsubst. *)
  (*     apply EqTySym. apply CongId ; assumption. *)
  (* } *)
  { admit. }
  assert (
    eqctx
    (ctxextend G
       (Subst
          (Subst (Id (Subst A (sbweak D A)) (subst u (sbweak D A)) (var 0))
             (sbshift G A sbs)) (sbzero G (Subst A sbs) (subst v sbs))))
    (ctxextend G (Subst (Id A u v) sbs))
  ).
  (* { now apply EqCtxExtend. } *)
  { admit. }
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
  (* Now let's proceed with the proof. *)
  gocompsubst. gocompsubst. gocompsubst.
  all:admit.
  (* - eapply SubstCtxConv ; magic. *)
  (* - gocompsubst. *)
  (*   + eapply SubstComp. *)
  (*     * magic. *)
  (*     * eapply SubstCtxConv ; magic. *)
  (*   + eapply CongTySubst. *)
  (*     * (* Now we're back to where we're supposed to be, *)
  (*              where the proof is in my notebook. *) *)
  (*       (* We go from the rhs. *) *)
  (*       { eapply SubstSym. eapply SubstTrans. *)
  (*         { (* Then we only look on the lhs of the composition. *) *)
  (*           eapply CongSubstComp. *)
  (*           - (* We exchange the substs. *) *)
  (*             eapply SubstSym. eapply ShiftZero ; assumption. *)
  (*           - (* We don't touch the rhs. *) *)
  (*             eapply SubstRefl. eassumption. *)
  (*         } *)
  (*         (* We're using associativity to look at the rhs. *) *)
  (*         eapply SubstTrans. *)
  (*         { eapply CompAssoc ; magic. } *)
  (*         (* We can now have a look at the rhs of the composition. *) *)
  (*         eapply SubstTrans. *)
  (*         { eapply CongSubstComp. *)
  (*           - (* On the left we remain unchanged. *) *)
  (*             eapply SubstRefl. magic. *)
  (*           - (* On the right we have a composition of shifts, thus we *)
  (*                use fonctoriality to progress. *)
  (*                However we need to apply congruence again to rewrite *)
  (*                the type in the left shift. *)
  (*              *) *)
  (*             eapply CongSubstComp. *)
  (*             + eapply @CongSubstShift *)
  (*               with (A2 := Subst *)
  (*                            (Id (Subst A (sbweak D A)) *)
  (*                                (subst u (sbweak D A)) *)
  (*                                (var 0)) *)
  (*                            (sbzero D A v) *)
  (*                    ). *)
  (*               * eassumption. *)
  (*               * eapply SubstRefl ; eassumption. *)
  (*               * apply EqTySym. assumption. *)
  (*             + (* We don't change the other substitution. *) *)
  (*               eapply SubstRefl. magic. *)
  (*         } *)
  (*         (* Now that we rewrote the type, we can use fonctoriality. *) *)
  (*         (* Note this could be meged with the next couple steps. *) *)
  (*         eapply SubstTrans. *)
  (*         { eapply CongSubstComp. *)
  (*           - (* On the left we remain unchanged. *) *)
  (*             eapply SubstRefl. magic. *)
  (*           - eapply EqSubstCtxConv. *)
  (*             + eapply CompShift ; magic. *)
  (*             + assumption. *)
  (*             + apply CtxRefl. assumption. *)
  (*         } *)
  (*         (* Now that we have a composition inside the shift, we want *)
  (*            to proceed with an exchange by using ShiftZero. *) *)
  (*         eapply SubstTrans. *)
  (*         { eapply CongSubstComp. *)
  (*           - (* We leave the left unchanged. *) *)
  (*             eapply SubstRefl. magic. *)
  (*           - eapply EqSubstCtxConv. *)
  (*             + eapply CongSubstShift. *)
  (*               * eassumption. *)
  (*               * eapply SubstSym. now eapply ShiftZero. *)
  (*               * apply EqTyRefl. assumption. *)
  (*             + assumption. *)
  (*             + apply CtxRefl. assumption. *)
  (*         } *)
  (*         (* Now we need to apply CompShift again to put the composition outside *)
  (*            and apply associativity. *) *)
  (*         eapply SubstTrans. *)
  (*         { eapply CongSubstComp. *)
  (*           - (* On the left we remain unchanged. *) *)
  (*             eapply SubstRefl. magic. *)
  (*           - eapply SubstSym. eapply EqSubstCtxConv. *)
  (*             + eapply CompShift ; magic. *)
  (*             + assumption. *)
  (*             + apply CtxRefl. assumption. *)
  (*         } *)
  (*         (* Now, it's time to apply associativity guys. *) *)
  (*         eapply SubstTrans. *)
  (*         { eapply SubstSym. eapply CompAssoc. *)
  (*           - magic. *)
  (*           - eapply SubstCtxConv. *)
  (*             + magic. *)
  (*             + assumption. *)
  (*             + eapply CtxRefl. assumption. *)
  (*           - magic. *)
  (*         } *)
  (*         (* Now we should finally have the same structure for the substitutions *)
  (*            and thus be able to apply congruences. *) *)
  (*         eapply CongSubstComp. *)
  (*         - eapply CongSubstComp. *)
  (*           + eapply CongSubstZero. *)
  (*             * eassumption. *)
  (*             * assumption. *)
  (*             * apply EqRefl. magic. *)
  (*           + { eapply EqSubstCtxConv. *)
  (*               - eapply CongSubstShift. *)
  (*                 + assumption. *)
  (*                 + eapply SubstRefl. magic. *)
  (*                 + apply EqTySym. assumption. *)
  (*               - apply EqCtxExtend. *)
  (*                 + assumption. *)
  (*                 + assumption. *)
  (*               - apply CtxRefl. assumption. *)
  (*             } *)
  (*         - apply SubstRefl. apply SubstShift. *)
  (*           + magic. *)
  (*           + assumption. *)
  (*       } *)
  (*     * eapply EqTyRefl. eassumption. *)
  Unshelve. all:assumption.
(* Defined. *)
Admitted.

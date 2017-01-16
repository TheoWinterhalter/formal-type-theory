(* Sanity theorems for ptt. *)

Require Import syntax.
Require Import ptt.
Require Import myptt ptt_tactics ptt_admissible.

Definition sane_issubst sbs G D :
  issubst sbs G D -> isctx G * isctx D.
Proof.
  intro H ; destruct H.

  (* SubstZero *)
  { split.

    - assumption.
    - now apply CtxExtend.
  }

  (* SubstWeak *)
  { split.

    - now apply CtxExtend.
    - assumption.
  }

  (* SubstShift *)
  { split.

    - apply CtxExtend.
      + assumption.
      + now apply (@TySubst G D).
    - now apply CtxExtend.
  }

  (* SubstId *)
  { split.
    - assumption.
    - assumption.
  }

  (* SubstComp *)
  { split.
    - assumption.
    - assumption.
  }

  (* SubstCtxConv *)
  { split.
    - assumption.
    - assumption.
  }
Defined.

Definition sane_istype G A :
  istype G A -> isctx G.
Proof.
  intro H; destruct H ; assumption.
Defined.

Definition sane_isterm' G u A :
  isterm G u A -> istype G A.
Proof.
  intro H ; destruct H.

  (* TermTyConv *)
  { assumption. }

  (* TermCtxConv *)
  { now apply (@TyCtxConv G D). }

  (* TermSubst *)
  { now apply (@TySubst G D A sbs). }

  (* TermVarZero *)
  { eapply TySubst.
    - now apply (@CtxExtend G A).
    - eassumption.
    - now eapply SubstWeak.
    - assumption.
  }

  (* TermVarSucc *)
  { apply (@TySubst (ctxextend G B) G).
    - now apply CtxExtend.
    - assumption.
    - now apply SubstWeak.
    - assumption.
  }

  (* TermAbs *)
  { now apply (@TyProd). }

  (* TermApp *)
  { apply (@TySubst G (ctxextend G A)).
    - assumption.
    - now apply CtxExtend.
    - now apply SubstZero.
    - assumption.
  }

  (* TermRefl *)
  { now apply TyId. }

  (* TermJ *)
  { apply @TySubst with (D := ctxextend G (Id A u v)) ; try magic.
    apply @TyCtxConv
      with (G :=
              ctxextend G
                        (Subst
                           (Id
                              (Subst A (sbweak G A))
                              (subst u (sbweak G A))
                              (var 0))
                           (sbzero G A v))).
    - magic3.
    - magic.
    - eapply myTySubst ; magic3.
    - apply EqCtxExtend ; try magic.
      assert (eqtype G A (Subst A (sbcomp (sbweak G A) (sbzero G A v)))).
      { apply compWeakZero ; assumption. }
      assert (eqtype G A (Subst (Subst A (sbweak G A)) (sbzero G A v))).
      { apply EqTyWeakZero ; assumption. }
      gopushsubst. apply CongId ; try magic.
      + eapply myTermTyConv.
        * eassumption.
        * assumption.
        * assumption.
        * assumption.
        * magic.
      + eapply myTermTyConv.
        * eassumption.
        * assumption.
        * assumption.
        * assumption.
        * magic.
      + { gocompsubst.
          - eapply myEqTrans.
            + eapply myCongTermSubst.
              * eapply WeakZero ; magic.
              * eapply EqRefl ; magic.
              * assumption.
              * assumption.
              * assumption.
              * assumption.
              * assumption.
              * magic.
              * magic.
            + eapply myEqTyConv.
              * eapply EqIdSubst ; eassumption.
              * assumption.
              * assumption.
              * assumption.
              * magic.
              * { eapply myTermTyConv.
                  - eapply myTermSubst.
                    + magic.
                    + eassumption.
                    + assumption.
                    + assumption.
                    + assumption.
                  - magic.
                  - assumption.
                  - magic.
                  - assumption.
                }
              * assumption.
            + assumption.
            + magic.
            + magic.
            + eapply myTermTyConv.
              * eapply myTermSubst ; try eassumption ; try magic.
              * eapply myCongTySubst ; try eassumption ; try magic.
              * assumption.
              * magic.
              * magic.
            + eapply myTermTyConv ; try eassumption ; try magic.
          - eapply myTermTyConv.
            + eapply myTermSubst.
              * magic.
              * eapply myTermSubst ; try eassumption ; try magic.
              * assumption.
              * magic.
              * magic.
            + gocompsubst. Unshelve. assumption.
            + assumption.
            + magic.
            + magic.
          - eapply myTermTyConv ; try eassumption ; try magic.
        }
      + eapply myEqTyConv ; try eassumption ; try magic.
        eapply myTermTyConv.
        * { eapply myTermSubst.
            - magic.
            - magic.
            - assumption.
            - magic.
            - magic.
          }
        * magic.
        * assumption.
        * magic.
        * assumption.
  }

  (* TermExfalso *)
  { assumption. }

  (* TermUnit *)
  { now apply TyUnit. }

  (* TermTrue *)
  { now apply TyBool. }

  (* TermFalse *)
  { now apply TyBool. }

  (* TermCond *)
  { eapply (@TySubst G (ctxextend G Bool)).
    + assumption.
    + apply CtxExtend.
      * assumption.
      * now apply TyBool.
    + apply SubstZero.
      * assumption.
      * now apply TyBool.
      * assumption.
    + assumption.
  }
Defined.


Definition sane_isterm G u A :
  isterm G u A -> isctx G * istype G A.
Proof.
  intro H.
  pose (K := sane_isterm' G u A H).
  split ; [now apply (@sane_istype G A) | assumption].
Defined.

Definition sane_eqtype' G A B :
  eqtype G A B -> istype G A * istype G B.
Proof.
  intro H ; destruct H.

  (* EqTyCtxConv *)
  { split.
    - { now apply (@TyCtxConv G D). }
    - { now apply (@TyCtxConv G D). }
  }

  (* EqTyRefl*)
  { split ; assumption. }

  (* EqTySym *)
  { split ; assumption. }

  (* EqTyTrans *)
  { split ; assumption. }

  (* EqTyIdSubst *)
  { split.
    - eapply TySubst.
      + assumption.
      + eassumption.
      + now apply SubstId.
      + assumption.
    - assumption.
  }

  (* EqTySubstComp *)
  { split.
    - apply (@TySubst G D) ; auto.
      apply (@TySubst D E) ; auto.
    - apply (@TySubst G E) ; auto.
      apply (@SubstComp G D E) ; auto.
  }

  (* EqTySubstProd *)
  { split.
    - { apply (@TySubst G D) ; auto using TyProd. }
    - { apply TyProd ; auto.
        + now apply (@TySubst G D).
        + apply (@TySubst _ (ctxextend D A)) ; auto.
          * apply CtxExtend ; auto.
            now apply (@TySubst G D).
          * now apply CtxExtend.
          * now apply SubstShift.
      }
  }

  (* EqTySubstId *)
  { split.
    - { apply (@TySubst G D) ; auto using TyId. }
    - { apply TyId ; auto using (@TySubst G D), (@TermSubst G D). }
  }

  (* EqTySubstEmpty *)
  { split.
    - { apply (@TySubst G D) ; auto using TyEmpty. }
    - { now apply TyEmpty. }
  }

  (* EqTySubstUnit *)
  { split.
    - { apply (@TySubst G D) ; auto using TyUnit. }
    - { now apply TyUnit. }
  }

  (* EqTySubstBool *)
  { split.
    - { apply (@TySubst G D) ; auto using TyBool. }
    - { now apply TyBool. }
  }

  (* EqTyExfalso *)
  { split ; assumption. }

  (* CongProd *)
  { split.
    - { now apply TyProd. }
    - { apply TyProd ; auto.
        apply (@TyCtxConv (ctxextend G A1)) ; auto using CtxExtend.
        apply EqCtxExtend ; auto using CtxRefl.
      }
  }

  (* CongId *)
  { split.
    - { now apply TyId. }
    - { apply TyId.
        - assumption.
        - assumption.
        - now apply (@TermTyConv G A B v1).
        - now apply (@TermTyConv G A B v2).
      }
  }

  (* CongTySubst *)
  { split.
    - { now apply (@TySubst G D). }
    - { now apply (@TySubst G D). }
  }

Defined.

Theorem sane_eqctx G D :
  eqctx G D -> isctx G * isctx D.
Proof.
  intro H ; destruct H.

  (* CtxRefl *)
  { split.
    - assumption.
    - assumption.
  }

  (* CtxSym *)
  { split.
    - assumption.
    - assumption.
  }

  (* CtxTrans *)
  { split.
    - assumption.
    - assumption.
  }

  (* EqCtxEmpty *)
  { split.
    - now apply CtxEmpty.
    - now apply CtxEmpty.
  }

  (* EqCtxExtend *)
  { split.
    - now apply CtxExtend.
    - apply CtxExtend.
      + assumption.
      + apply (@TyCtxConv G D) ; auto.
  }

Defined.


Theorem sane_eqtype G A B :
  eqtype G A B -> isctx G * istype G A * istype G B.
Proof.
  intro H.
  destruct (sane_eqtype' G A B H).
  auto using (sane_istype G A).
Defined.

Theorem sane_eqsubst' sbs sbt G D :
  eqsubst sbs sbt G D -> issubst sbs G D * issubst sbt G D.
Proof.
  intro H ; destruct H.

  (* SubstRefl *)
  - { split.
      - assumption.
      - assumption.
    }

  (* SubstSym *)
  - { split.
      - assumption.
      - assumption.
    }

  (* SubstTrans *)
  - { split.
      - assumption.
      - assumption.
    }

  (* CongSubstZero *)
  - { split.
      - now apply SubstZero.
      - apply (@SubstCtxConv G2 G1 (ctxextend G2 A2) (ctxextend G1 A1)) ;
          auto using CtxExtend, CtxRefl, CtxSym.
        + apply CtxExtend ; auto using (@TyCtxConv G1 G2).
        + apply SubstZero ;
            auto using (@TyCtxConv G1 G2), (@TermCtxConv G1 G2), (@TermTyConv G1 A1 A2).
        + apply EqCtxExtend ;
            auto using (@TyCtxConv G1 G2), CtxSym, (@EqTyCtxConv G1 G2), EqTySym.
    }

  (* CongSubstWeak *)
  - { split.
      - now apply SubstWeak.
      - apply (@SubstCtxConv (ctxextend G2 A2) (ctxextend G1 A1) G2 G1) ;
          auto using CtxExtend, CtxRefl.
        + apply CtxExtend ; auto.
          now apply (@TyCtxConv G1 G2).
        + apply SubstWeak ; auto.
          now apply (@TyCtxConv G1, G2).
        + apply EqCtxExtend ; auto using (@TyCtxConv G1 G2), CtxSym.
          apply (@EqTyCtxConv G1 G2) ; auto using EqTySym.
        + now apply CtxSym.
    }

  (* CongSubstShift *)
  - { split.
      - now apply SubstShift.
      - apply (@SubstCtxConv (ctxextend G2 (Subst A2 sbs2)) _ (ctxextend D A2) _) ;
          auto using CtxExtend.
        + apply CtxExtend ; auto.
          apply (@TyCtxConv G1 G2) ; auto.
          now apply (@TySubst G1 D).
        + apply CtxExtend ; auto.
          now apply (@TySubst G1 D).
        + apply SubstShift ; auto.
          apply (@SubstCtxConv G1 _ D D) ; auto using CtxRefl.
        + apply EqCtxExtend ; auto.
          * apply (@TySubst G2 D) ; auto.
            apply (@SubstCtxConv G1 _ D D); auto using CtxRefl.
          * apply (@TyCtxConv G1 G2); auto.
            now apply (@TySubst G1 D).
          * now apply CtxSym.
          * apply (@EqTyCtxConv G1 G2); auto using (@TySubst G1 D).
            apply (@CongTySubst G1 D) ; auto using EqTySym, SubstSym.
        + apply EqCtxExtend ; auto using EqTySym, CtxRefl.
    }

  (* CongSubstComp *)
  - { split.
      - now apply (@SubstComp G D E).
      - now apply (@SubstComp G D E).
    }

  (* EqSubstCtxConv *)
  - { split.
      - now apply (@SubstCtxConv G1 G2 D1 D2).
      - now apply (@SubstCtxConv G1 G2 D1 D2).
    }

  (* CompAssoc *)
  - { split.
      - apply (@SubstComp G E F) ; auto.
        now apply (@SubstComp G D E).
      - apply (@SubstComp G D F); auto.
        now apply (@SubstComp D E F).
    }

  (* WeakNat *)
  - { split.
      - apply (@SubstComp _ (ctxextend D A)) ;
          auto using CtxExtend, (@TySubst G D), SubstShift, SubstWeak.
      - apply (@SubstComp _ G) ;
          auto using CtxExtend, (@TySubst G D), SubstWeak.
    }

  (* WeakZero *)
  - { split.
      - apply (@SubstComp _ (ctxextend G A)) ;
          auto using CtxExtend, SubstZero, SubstWeak.
      - now apply SubstId.
    }

  (* ShiftZero *)
  - { split.
      - apply (@SubstComp _ (ctxextend G (Subst A sbs))) ;
          auto using CtxExtend, (@TySubst G D), SubstZero, (@TermSubst G D), SubstShift.
      - apply (@SubstComp _ D) ;
          auto using CtxExtend, SubstZero.
    }

  (* CompShift *)
  - { split.
      - apply (@SubstComp _ (ctxextend D (Subst A sbt))) ;
          auto using CtxExtend, (@TySubst D E), SubstShift.
        + apply CtxExtend ; auto.
          apply (@TySubst G E) ; auto using (@SubstComp G D E).
        + { apply (@SubstCtxConv (ctxextend G (Subst (Subst A sbt) sbs)) _
                                 (ctxextend D (Subst A sbt))) ;
            auto using CtxExtend, (@TySubst D E), (@TySubst G D), (@TySubst G E),
                       (@SubstComp G D E), SubstShift, CtxRefl.
            apply EqCtxExtend ;
                auto using CtxRefl, (@TySubst G D), (@TySubst D E),
                           (@TySubst G E), (@SubstComp G D E).
              now apply (@EqTySubstComp G D E).
          }
      - apply SubstShift ; auto using (@SubstComp G D E).
    }

  (* CompIdRight *)
  - { split.
      - apply (@SubstComp G G D) ; auto using SubstId.
      - assumption.
    }

  (* CompIdLeft *)
  - { split.
      - apply (@SubstComp G D D) ; auto using SubstId.
      - assumption.
    }
Defined.

Theorem sane_eqsubst sbs sbt G D :
  eqsubst sbs sbt G D -> isctx G * isctx D * issubst sbs G D * issubst sbt G D.
Proof.
  intro H.
  destruct (sane_eqsubst' sbs sbt G D H).
  auto using (sane_issubst sbs G D).
Defined.

Theorem sane_eqterm' G u v A :
  eqterm G u v A -> isterm G u A * isterm G v A.
Proof.
  intro H ; destruct H.

  (* EqTyConv *)
  - { split.
      - { now apply (@TermTyConv G A B u). }
      - { now apply (@TermTyConv G A B v). }
    }

  (* EqCtxConv *)
  - { split.
      - { now apply (@TermCtxConv G D A). }
      - { now apply (@TermCtxConv G D A). }
    }

  (* EqRefl *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* EqSym *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* EqTrans *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* EqIdSubst *)
  - { split.
      - { apply (@TermTyConv G (Subst A (sbid G)) A).
          - assumption.
          - apply (@TySubst G G) ; auto using SubstId.
          - assumption.
          - apply (@TermSubst G G) ; auto using SubstId.
          - now apply EqTyIdSubst.
        }
      - { assumption. }
    }

  (* EqSubstComp *)
  - { split.
      - { apply (@TermTyConv G (Subst (Subst A sbt) sbs) (Subst A (sbcomp sbt sbs))).
          - assumption.
          - apply (@TySubst G D) ; auto.
            now apply (@TySubst D E).
          - apply (@TySubst G E) ; auto.
            now apply (@SubstComp G D E).
          - apply (@TermSubst G D) ; auto.
            + now apply (@TySubst D E).
            + now apply (@TermSubst D E).
          - now apply (@EqTySubstComp G D E).
        }
      - { apply (@TermSubst G E) ; auto.
          now apply (@SubstComp G D E).
        }
    }

  (* EqSubstWeak *)
  - { split.
      - { apply (@TermSubst _ G) ; auto using CtxExtend.
          now apply SubstWeak.
        }
      - { now apply TermVarSucc. }
    }


  (* EqSubstZeroZero *)
  - { split.
      - { apply (@TermTyConv G (Subst (Subst A (sbweak G A)) (sbzero G A u))).
          - assumption.
          - apply (@TySubst _ (ctxextend G A)) ; auto using CtxExtend.
            + now apply SubstZero.
            + apply (@TySubst _ G) ; auto using CtxExtend.
              now apply SubstWeak.
          - assumption.
          - apply (@TermSubst _ (ctxextend G A)) ; auto using CtxExtend.
            + apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
            + now apply SubstZero.
            + now apply TermVarZero.
          - apply (@EqTyTrans G _ (Subst A (sbid G))) ; auto.
            + apply (@TySubst _ (ctxextend G A)) ; auto using CtxExtend.
              * now apply SubstZero.
              * apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
            + apply (@TySubst _ G) ; auto using SubstId.
            + { apply (@EqTyTrans _ _ (Subst A (sbcomp (sbweak G A) (sbzero G A u)))) ; auto.
                - apply (@TySubst _ (ctxextend G A)) ; auto using CtxExtend, SubstZero.
                  apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
                - apply (@TySubst _ G) ; auto.
                  + apply (@SubstComp _ (ctxextend G A)) ; auto using CtxExtend, SubstWeak, SubstZero.
                - apply (@TySubst _ G) ; auto using SubstId.
                - apply (@EqTySubstComp G (ctxextend G A) G) ;
                  auto using CtxExtend, (@SubstComp G (ctxextend G A)) , SubstWeak, SubstZero.
                - apply (@CongTySubst G G) ;
                  auto using CtxExtend, (@SubstComp G (ctxextend G A)) , SubstWeak, SubstZero, SubstId, EqTyRefl, WeakZero.
              }
            + now apply EqTyIdSubst.
        }
      - { assumption. }
    }

  (* EqSubstZeroSucc *)
  - { split.
      - { apply (@TermTyConv G (Subst (Subst A (sbweak G B)) (sbzero G B u))).
          - assumption.
          - apply (@TySubst _ (ctxextend G B)) ; auto using CtxExtend, SubstZero.
            apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
          - assumption.
          - apply (@TermSubst G (ctxextend G B)) ; auto using CtxExtend.
            + apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
            + now apply SubstZero.
            + now apply TermVarSucc.
          - apply EqTySym ; try magic.
            apply EqTyWeakZero ; magic.
        }
      - { assumption. }
    }

  (* EqSubstShiftZero *)
  - { split.
      - { eapply myTermTyConv.
          - eapply myTermSubst.
            + eapply mySubstShift ; eassumption.
            + magic.
            + constructor.
              * assumption.
              * eapply myTySubst ; eassumption.
            + eapply myTySubst ; try eassumption ; magic.
            + magic.
          - apply EqTyWeakNat ; magic.
          - constructor.
            + assumption.
            + eapply myTySubst ; eassumption.
          - eapply myTySubst.
            + eapply mySubstShift ; eassumption.
            + eapply myTySubst ; magic.
            + constructor.
              * assumption.
              * eapply myTySubst ; eassumption.
            + magic.
          - eapply myTySubst.
            + eapply SubstWeak.
              * assumption.
              * eapply myTySubst ; eassumption.
            + eapply myTySubst ; eassumption.
            + constructor. (* There may be room for maigc improvement here *)
              * assumption.
              * eapply myTySubst ; eassumption.
            + magic.
        }
      - { magic. }
    }

  (* EqSubstShiftSucc *)
  - { split.
      - { eapply myTermTyConv ; [
            (eapply myTermSubst ; try magic) ;
            (eapply TermVarSucc ; try magic) ;
            eassumption
          | try magic ..
          ].
          apply EqTyWeakNat ; magic.
        }
      - { magic. }
    }

  (* EqSubstAbs *)
  - { split.
      - { eapply myTermTyConv ; [
            eapply myTermSubst ; magic
          | try magic ..
          ].
          gopushsubst.
        }
      - { magic. }
    }

  (* EqSubstApp *)
  - { split.
      - { magic. }
      - { eapply myTermTyConv ; [
            (eapply TermApp ; try magic) ;
            (eapply myTermTyConv ; [
              (eapply myTermSubst ; try eassumption) ; magic
            | try magic ..
            ]) ;
            gopushsubst
          | try magic ..
          ].
          apply EqTyShiftZero ; magic.
          Unshelve. all:magic.
        }
    }

  (* EqSubstRefl *)
  - { split.
      - { eapply myTermTyConv ; [
            eapply myTermSubst ; magic
          | try magic ..
          ].
          gopushsubst.
        }
      - { magic. }
    }

  (* EqSubstJ *)
  - { split.
      - { eapply myTermSubst ; try magic.
          eapply myTySubst ; try magic.
          eapply myTySubst ; try magic.
          eapply mySubstCtxConv ; try magic.
          - apply EqCtxExtend ; try magic.
            gopushsubst.
            apply CongId ; try magic.
            + eapply myTermTyConv ; [ eassumption | try magic .. ].
              apply EqTyWeakZero ; magic.
            + eapply myTermTyConv ; [ eassumption | try magic .. ].
              apply EqTyWeakZero ; magic.
            + apply myEqTySym ; [
                apply EqTyWeakZero ; magic
              | magic ..
              ].
            + apply EqSubstWeakZero ; try magic.
              eapply myTermTyConv ; [ eassumption | try magic .. ].
              apply EqTyWeakZero ; magic.
            + eapply myEqTyConv ; [
                eapply EqSubstZeroZero ; magic
              | try magic ..
              ].
              * apply EqTyWeakZero ; magic.
              * eapply myTermTyConv ; [
                  eapply myTermSubst ; magic
                | try magic ..
                ].
                apply myEqTySym ; [
                  apply EqTyWeakZero ; magic
                | magic ..
                ].
          - apply CtxRefl ; magic.
        }
      - { eapply myTermTyConv.
          - eapply TermJ ; try magic.
            + eapply myTySubst ; try magic.
              eapply mySubstCtxConv ; try magic.
              * apply EqCtxExtend ; try magic.
                gopushsubst.
                { eapply CongId ; try magic.
                  - eapply myTermTyConv.
                    + eapply myTermSubst ; try magic.
                      eapply myTermSubst ; try magic.
                      eassumption.
                    + apply myEqTySym ; try magic.
                      apply EqTyWeakNat ; magic.
                    + magic.
                    + magic.
                    + magic.
                  - eapply myTermTyConv ; [
                      eapply TermVarZero ; magic
                    | try magic ..
                    ].
                    apply myEqTySym ; try magic.
                    apply EqTyWeakNat ; magic.
                  - apply EqTyWeakNat ; magic.
                  - eapply myEqTyConv ; [
                      eapply EqSubstWeakNat ; try magic
                    | try magic ..
                    ].
                    + eassumption.
                    + apply myEqTySym ; try magic.
                      apply EqTyWeakNat ; magic.
                    + eapply myTermTyConv ; [
                        eapply myTermSubst ; try magic
                      | try magic ..
                      ].
                      * eapply myTermSubst ; try magic.
                        eassumption.
                      * apply EqTyWeakNat ; magic.
                    + magic.
                  - eapply myEqTyConv ; [
                      eapply EqSubstShiftZero ; magic
                    | try magic ..
                    ].
                    + apply myEqTySym ; try magic.
                      apply EqTyWeakNat ; magic.
                    + eapply myTermTyConv ; [
                        eapply myTermSubst ; magic
                      | try magic ..
                      ].
                      apply EqTyWeakNat ; magic.
                }
              * apply CtxRefl ; magic.
            + eapply myTermTyConv ; [
                eapply myTermSubst ; try magic
              | try magic ..
              ].
              * eassumption.
              * (* This seems to be what used to be called JTyConv! *)
                admit.
              * eapply TySubst ; try magic.
                eapply TySubst ; try magic.
                { eapply mySubstCtxConv ; try magic.
                  - apply EqCtxExtend ; try magic.
                    gopushsubst.
                    apply CongId ; try magic.
                    + eapply myTermTyConv ; [
                        eapply myTermSubst ; try magic
                      | try magic ..
                      ].
                      * eassumption.
                      * apply EqTyWeakZero ; magic.
                    + eapply myTermTyConv ; [
                        eapply myTermSubst ; try magic
                      | try magic ..
                      ].
                      * eassumption.
                      * apply EqTyWeakZero ; magic.
                    + apply myEqTySym ; try magic.
                      apply EqTyWeakZero ; magic.
                    + eapply myEqTyConv ; [
                        eapply EqSubstWeakZero ; try magic
                      | try magic ..
                      ].
                      * eapply myTermTyConv ; [
                          eapply myTermSubst ; try magic ; try eassumption
                        | try magic ..
                        ].
                        apply EqTyWeakZero ; magic.
                      * eapply myTermTyConv ; [
                          eapply myTermSubst ; try magic ; try eassumption
                        | try magic ..
                        ].
                        apply EqTyWeakZero ; magic.
                    + eapply myEqTyConv ; [
                        eapply EqSubstZeroZero ; magic
                      | try magic ..
                      ].
                      * apply EqTyWeakZero ; magic.
                      * eapply myTermTyConv ; [
                          eapply myTermSubst ; try magic ; try eassumption
                        | try magic ..
                        ].
                        apply myEqTySym ; try magic.
                        apply EqTyWeakZero ; magic.
                  - apply EqCtxExtend ; try magic.
                    gopushsubst.
                    apply CongId ; try magic.
                    + eapply myTermTyConv ; [
                        eapply myTermSubst ; try magic
                      | try magic ..
                      ].
                      * eapply myTermSubst ; try magic.
                        eassumption.
                      * apply myEqTySym ; try magic.
                        apply EqTyWeakNat ; magic.
                    + eapply myTermTyConv ; [
                        eapply TermVarZero ; magic
                      | try magic ..
                      ].
                      apply myEqTySym ; try magic.
                      apply EqTyWeakNat ; magic.
                    + apply EqTyWeakNat ; magic.
                    + eapply myEqTyConv ; [
                        eapply EqSubstWeakNat ; try magic
                      | try magic ..
                      ].
                      * eassumption.
                      * apply myEqTySym ; try magic.
                        apply EqTyWeakNat ; magic.
                      * { eapply myTermTyConv ; [
                            eapply myTermSubst ; try magic
                          | try magic ..
                          ].
                          - eapply myTermSubst ; try magic.
                            eassumption.
                          - apply EqTyWeakNat ; magic.
                        }
                      * magic.
                    + eapply myEqTyConv ; [
                        eapply EqSubstShiftZero ; magic
                      | try magic ..
                      ].
                      * apply myEqTySym ; try magic.
                        apply EqTyWeakNat ; magic.
                      * admit.
                }
            + admit.
          - admit. (* Still JTyConv? *)
          - assumption.
          - admit.
          - admit.
        }
        Unshelve. all:try assumption. all:try magic.
        + admit.
        + admit.
    }

  (* EqSubstExfalso *)
  - { split.
      - { magic. }
      - { eapply myTermTyConv ; [
            apply TermExfalso ; try magic
          | try magic ..
          ].
          eapply myTermTyConv ; [
            eapply myTermSubst ; try magic
          | try magic ..
          ].
          - eassumption.
          - gopushsubst.
        }
    }

  (* EqSubstUnit *)
  - { split.
      - { eapply myTermTyConv ; [
            eapply myTermSubst ; try magic
          | try magic ..
          ].
          gopushsubst.
        }
      - { magic. }
    }

  (* EqSubstTrue *)
  - { split.
      - { eapply myTermTyConv ; [
            eapply myTermSubst ; try magic
          | try magic ..
          ].
          gopushsubst.
        }
      - { magic. }
    }

  (* EqSubstFalse *)
  - { split.
      - { eapply myTermTyConv ; [
            eapply myTermSubst ; try magic
          | try magic ..
          ].
          gopushsubst.
        }
      - { magic. }
    }

  (* EqSubstCond *)
  - { split.
      - { magic. }
      - { eapply myTermTyConv ; [
            apply TermCond ; try magic
          | try magic ..
          ].
          - eapply myTermTyConv ; [
              eapply myTermSubst ; try magic
            | try magic ..
            ].
            + eassumption.
            + gopushsubst.
          - eapply myTySubst ; try magic.
            eapply mySubstCtxConv ; try magic.
            + apply EqCtxExtend ; try magic ; try gopushsubst.
            + apply CtxRefl ; magic.
          - eapply myTermTyConv ; [
              eapply myTermSubst ; try magic
            | try magic ..
            ].
            + eassumption.
            + apply EqTySym ; try magic.
              * eapply myTySubst ; try magic.
                eapply myTySubst ; try magic.
                { eapply mySubstCtxConv ; try magic.
                  - apply EqCtxExtend ; try magic ; try gopushsubst.
                  - apply CtxRefl ; magic.
                }
              * { apply EqTySym ; try magic.
                  - eapply myTySubst ; try magic.
                    eapply myTySubst ; try magic.
                    eapply mySubstCtxConv ; try magic.
                    + apply EqCtxExtend ; try magic ; try gopushsubst.
                    + apply CtxRefl ; magic.
                  - eapply myEqTyTrans ; [
                      eapply myEqTySym ; [
                        eapply EqTyShiftZero ; magic
                      | magic ..
                      ]
                    | try magic ..
                    ].
                    + eapply myCongTySubst ; try magic.
                      * { eapply myCongSubstZero ; try magic.
                          - gopushsubst.
                          - gopushsubst.
                            + eapply myTermTyConv ; [
                                eapply myTermSubst ; magic
                              | try magic ; try gopushsubst ..
                              ].
                            + gopushsubst.
                            + eapply myTermTyConv ; [
                                eapply myTermSubst ; magic
                              | try magic ; try gopushsubst ..
                              ].
                          - eapply myTermTyConv ; try magic.
                            gopushsubst.
                        }
                      * eapply mySubstCtxConv ; try magic.
                        apply EqCtxExtend ; try magic.
                        gopushsubst.
                    + eapply myTySubst ; try magic.
                      eapply myTySubst ; try magic.
                      eapply mySubstCtxConv ; try magic.
                      * apply EqCtxExtend ; try magic.
                        gopushsubst.
                      * apply CtxRefl ; magic.
                }
            + eapply myTySubst ; try magic.
              eapply myTySubst ; try magic.
              eapply mySubstCtxConv ; try magic.
              * apply EqCtxExtend ; try magic.
                gopushsubst.
              * apply CtxRefl ; magic.
          - eapply myTermTyConv ; [
              eapply myTermSubst ; [ eassumption | eassumption | magic .. ]
            | try magic ..
            ].
            + { eapply myEqTyTrans ; [
                  eapply myEqTySym ; [
                    eapply EqTyShiftZero ; magic
                  | magic ..
                  ]
                | try magic ..
                ].
                - eapply myCongTySubst ; try magic.
                  + { eapply myCongSubstZero ; try magic.
                      - gopushsubst.
                      - gopushsubst.
                        + eapply myTermTyConv ; [
                            eapply myTermSubst ; magic
                          | try magic ; try gopushsubst ..
                          ].
                        + gopushsubst.
                        + eapply myTermTyConv ; [
                            eapply myTermSubst ; magic
                          | try magic ; try gopushsubst ..
                          ].
                      - eapply myTermTyConv ; try magic.
                        gopushsubst.
                    }
                  + eapply mySubstCtxConv ; try magic.
                    apply EqCtxExtend ; try magic.
                    gopushsubst.
                - eapply myTySubst ; try magic.
                  eapply myTySubst ; try magic.
                  eapply mySubstCtxConv ; try magic.
                  + apply EqCtxExtend ; try magic.
                    gopushsubst.
                  + apply CtxRefl ; magic.
              }
            + eapply myTySubst ; try magic.
              eapply myTySubst ; try magic.
              eapply mySubstCtxConv ; try magic.
              * apply EqCtxExtend ; try magic. gopushsubst.
              * apply CtxRefl ; magic.
          - { apply EqTySym ; try magic.
              - eapply myTySubst ; try magic.
                eapply mySubstCtxConv ; try magic.
                + eapply SubstZero ; try magic.
                  eapply myTermTyConv ; [
                    eapply myTermSubst ; [ eassumption | eassumption | magic ..]
                    | try magic ..
                  ].
                  gopushsubst.
                + apply CtxRefl ; magic.
                + apply EqCtxExtend ; try magic ; try gopushsubst.
              - eapply myEqTyTrans ; [
                  eapply myEqTySym ; [
                    eapply EqTyShiftZero ; magic
                  | magic ..
                  ]
                | try magic ..
                ].
                + eapply myCongTySubst ; try magic.
                  * eapply myCongSubstZero ; try magic.
                    gopushsubst.
                  * { eapply mySubstCtxConv ; try magic.
                      - eapply SubstZero ; try magic.
                        eapply myTermTyConv ; [
                          eapply myTermSubst ;
                          [ eassumption | eassumption | magic ..]
                        | try magic ..
                        ].
                        gopushsubst.
                      - apply CtxRefl ; magic.
                      - apply EqCtxExtend ; try magic ; try gopushsubst.
                    }
                + eapply myTySubst ; try magic.
                  eapply mySubstCtxConv ; try magic.
                  * eapply SubstZero ; try magic.
                    eapply myTermTyConv ; [
                      eapply myTermSubst ; [ eassumption | eassumption | magic ..]
                    | try magic ..
                    ].
                    gopushsubst.
                  * apply CtxRefl ; magic.
                  * apply EqCtxExtend ; try magic ; try gopushsubst.
            }
          - eapply myTySubst ; try magic.
            eapply mySubstCtxConv ; try magic.
            * eapply SubstZero ; try magic.
              eapply myTermTyConv ; [
                eapply myTermSubst ; [ eassumption | eassumption | magic ..]
              | try magic ..
              ].
              gopushsubst.
            * apply CtxRefl ; magic.
            * apply EqCtxExtend ; try magic ; try gopushsubst.
        }
        Unshelve. all:magic.
    }

  (* EqTermExfalso *)
  - { split.
      - { assumption. }
      - { assumption. }
    }

  (* UnitEta *)
  - { split.
      - { assumption. }
      - { magic. }
    }

  (* EqReflection *)
  - { split.
      - { assumption. }
      - { magic. }
    }

  (* ProdBeta *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CondTrue *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CondFalse *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* ProdEta *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* JRefl *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongAbs *)
  - { split.
      - { magic. }
      - { eapply myTermTyConv ; [
            eapply TermAbs ; try magic
          | magic ..
          ].
          eapply myTermCtxConv ; [
            eapply myTermTyConv ; [
              eassumption
            | magic ..
            ]
          | magic ..
          ].
        }
    }

  (* CongApp *)
  - { split.
      - { magic. }
      - { eapply myTermTyConv ; [
            eapply TermApp ; try magic
          | try magic ..
          ].
          - eapply myTermTyConv ; [
              eassumption
            | magic ..
            ].
          - eapply myTermTyConv ; [
              eassumption
            | magic ..
            ].
          - eapply myCongTySubst ; try magic.
            + eapply myEqSubstCtxConv ; [
               eapply myCongSubstZero ; try magic
              | try magic ..
              ].
              * eapply myEqTyConv ; [
                  eapply EqSym ; try magic ; try eassumption
                | magic ..
                ].
              * eapply myTermTyConv ; [
                  eassumption
                | magic ..
                ].
              * eapply myTermTyConv ; [
                  eassumption
                | magic ..
                ].
              * eapply SubstZero ; try magic.
                eapply myTermTyConv ; [
                  eassumption
                | magic ..
                ].
              * eapply SubstCtxConv ; magic.
            + magic.
            + eapply SubstCtxConv ; try magic.
              * eapply SubstZero ; try magic.
                eapply myTermTyConv ; [
                  eassumption
                | magic ..
                ].
              * magic.
              * magic.
          - eapply myTySubst.
            + eapply SubstZero ; try magic.
              eapply myTermTyConv ; [
                eassumption
              | magic ..
              ].
            + magic.
            + magic.
            + magic.
        }
        Unshelve. all:magic.
        Unshelve. all:eapply myTyCtxConv ; [ eassumption | magic .. ].
    }

  (* CongRefl *)
  - { split.
      - { magic. }
      - { eapply myTermTyConv ; [
            eapply TermRefl ; try magic
          | try magic ..
          ].
          - eapply myTermTyConv ; [ eassumption | magic .. ].
          - apply CongId ; try magic.
            + eapply myTermTyConv ; [ eassumption | magic .. ].
            + eapply myTermTyConv ; [ eassumption | magic .. ].
            + eapply myTermTyConv ; [ eassumption | magic .. ].
            + eapply myTermTyConv ; [ eassumption | magic .. ].
            + eapply myEqTyConv ; [
                eapply myEqSym ; [ eassumption | magic .. ]
              | magic ..
              ].
            + eapply myEqTyConv ; [
                eapply myEqSym ; [ eassumption | magic .. ]
              | magic ..
              ].
          - apply TyId ; try magic.
            + eapply myTermTyConv ; [ eassumption | magic .. ].
            + eapply myTermTyConv ; [ eassumption | magic .. ].
        }
    }

  (* CongJ *)
  - { split.
      - { eapply myTermTyConv ; [
            eapply TermJ ; try magic
          | try magic ..
          ].
          - apply EqTyRefl ; try magic.
            eapply myTySubst ; try magic.
            eapply myTySubst ; try magic.
            eapply mySubstCtxConv ; [
              eapply mySubstShift ; magic
            | try magic ..
            ].
            + apply EqCtxExtend ; try magic.
              gopushsubst.
              eapply CongId ; try magic.
              * eapply myTermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply myTermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * apply myEqTySym ; try magic.
                apply EqTyWeakZero ; magic.
              * apply EqSubstWeakZero ; try magic.
                eapply myTermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply myEqTyConv ; [
                  eapply EqSubstZeroZero ; magic
                | try magic ..
                ].
                { apply EqTyWeakZero ; magic. }
                { eapply myTermTyConv ; [
                    eapply myTermSubst ; magic
                  | try magic ..
                  ].
                  apply myEqTySym ; try magic.
                  apply EqTyWeakZero ; magic.
                }
            + apply CtxRefl ; magic.
          - eapply myTySubst ; try magic.
            eapply myTySubst ; try magic.
            eapply mySubstCtxConv ; [
              eapply mySubstShift ; magic
            | try magic ..
            ].
            + apply EqCtxExtend ; try magic.
              gopushsubst.
              eapply CongId ; try magic.
              * eapply myTermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply myTermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * apply myEqTySym ; try magic.
                apply EqTyWeakZero ; magic.
              * apply EqSubstWeakZero ; try magic.
                eapply myTermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply myEqTyConv ; [
                  eapply EqSubstZeroZero ; magic
                | try magic ..
                ].
                { apply EqTyWeakZero ; magic. }
                { eapply myTermTyConv ; [
                    eapply myTermSubst ; magic
                  | try magic ..
                  ].
                  apply myEqTySym ; try magic.
                  apply EqTyWeakZero ; magic.
                }
            + apply CtxRefl ; magic.
          - eapply myTySubst ; try magic.
            eapply myTySubst ; try magic.
            eapply mySubstCtxConv ; [
              eapply mySubstShift ; magic
            | try magic ..
            ].
            + apply EqCtxExtend ; try magic.
              gopushsubst.
              eapply CongId ; try magic.
              * eapply myTermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply myTermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * apply myEqTySym ; try magic.
                apply EqTyWeakZero ; magic.
              * apply EqSubstWeakZero ; try magic.
                eapply myTermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply myEqTyConv ; [
                  eapply EqSubstZeroZero ; magic
                | try magic ..
                ].
                { apply EqTyWeakZero ; magic. }
                { eapply myTermTyConv ; [
                    eapply myTermSubst ; magic
                  | try magic ..
                  ].
                  apply myEqTySym ; try magic.
                  apply EqTyWeakZero ; magic.
                }
            + apply CtxRefl ; magic.
          Unshelve. all:magic.
        }
      - { (* Some preliminary results to just get the types right. *)
          assert (isterm G u2 A2).
          { eapply myTermTyConv ; [ eassumption | magic .. ]. }
          assert (isterm G v2 A2).
          { eapply myTermTyConv ; [ eassumption | magic .. ]. }
          assert (isterm G p2 (Id A2 u2 v2)).
          { eapply myTermTyConv ; [ eassumption | magic .. ]. }
          assert (isterm G (refl A2 u2) (Id A1 u1 u1)).
          { eapply myTermTyConv ; [ eapply TermRefl ; magic | magic .. ]. }
          assert (issubst (sbweak G A2) (ctxextend G A1) G).
          { eapply mySubstCtxConv ; magic. }
          assert (istype (ctxextend G A1) (Subst A2 (sbweak G A2))).
          { eapply myTySubst ; try magic ; try eassumption. }
          assert (eqsubst (sbweak G A2) (sbweak G A1) (ctxextend G A1) G).
          { eapply SubstSym ; try magic. }
          assert (
            eqtype (ctxextend G A1)
                   (Subst A2 (sbweak G A2))
                   (Subst A1 (sbweak G A1))
          ).
          { eapply myCongTySubst ; try eassumption ; magic. }
          assert (
            isterm (ctxextend G A1)
                   (subst u2 (sbweak G A2)) (Subst A1 (sbweak G A1))
          ).
          { eapply myTermTyConv ; [
              eapply myTermSubst ; try magic ; try eassumption
            | try magic ; eassumption ..
            ].
          }
          assert (
            eqterm (ctxextend G A1)
                   (subst u1 (sbweak G A1))
                   (subst u2 (sbweak G A2))
                   (Subst A1 (sbweak G A1))
          ).
          { eapply myCongTermSubst ; magic. }
          assert (
            eqtype
              (ctxextend G A1)
              (Id (Subst A1 (sbweak G A1)) (subst u1 (sbweak G A1)) (var 0))
              (Id (Subst A2 (sbweak G A2)) (subst u2 (sbweak G A2)) (var 0))
          ).
          { eapply CongId ; try eassumption ; try magic. }
          assert (issubst (sbzero G A2 u2) G (ctxextend G A1)).
          { eapply mySubstCtxConv ; magic. }
          assert (isterm (ctxextend G A1) (var 0) (Subst A2 (sbweak G A2))).
          { eapply myTermTyConv ; [
              eapply TermVarZero ; magic
            | magic ..
            ].
          }
          assert (
            eqtype G A1 (Subst (Subst A1 (sbweak G A1)) (sbzero G A1 u1))
          ).
          { apply EqTyWeakZero ; magic. }
          assert (
            isterm G u1 (Subst (Subst A1 (sbweak G A1)) (sbzero G A1 u1))
          ).
          { eapply myTermTyConv ; [ eassumption | magic .. ]. }
          assert (
            eqterm G
                   (subst (subst u1 (sbweak G A1)) (sbzero G A1 u1))
                   u1
                   (Subst (Subst A1 (sbweak G A1)) (sbzero G A1 u1))
          ).
          { eapply EqSubstWeakZero ; magic. }
          assert (isterm G (subst (var 0) (sbzero G A1 u1)) A1).
          { eapply myTermTyConv ; [
              eapply myTermSubst ; magic
            | magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (var 0) (sbzero G A1 u1))
                   u1
                   (Subst (Subst A1 (sbweak G A1)) (sbzero G A1 u1))
          ).
          { eapply myEqTyConv ; [
              eapply EqSubstZeroZero ; magic
            | try magic ..
            ].
          }
          assert (
            eqtype G
                   (Subst (Id (Subst A1 (sbweak G A1))
                              (subst u1 (sbweak G A1))
                              (var 0)
                          )
                          (sbzero G A1 u1)
                   )
                   (Id A1 u1 u1)
          ).
          { gopushsubst. }
          assert (
            eqtype G A2 (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 u2))
          ).
          { apply EqTyWeakZero ; magic. }
          assert (
            eqtype G (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 u2)) A1
          ).
          { eapply myEqTyTrans ; [
              eapply myEqTySym ; [ eassumption | magic .. ]
            | magic ..
            ].
          }
          assert (
            isterm G u1 (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 u2))
          ).
          { eapply myTermTyConv ; [ eassumption | magic .. ]. }
          assert (
            isterm G u2 (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 u2))
          ).
          { eapply myTermTyConv ; [ eassumption | magic .. ]. }
          assert (
            eqterm G u2 u1 (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 u2))
          ).
          { eapply myEqSym ; [
              eapply myEqTyConv ; [ eassumption | magic .. ]
            | magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (subst u2 (sbweak G A2)) (sbzero G A2 u2))
                   u2
                   (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 u2))
          ).
          { eapply EqSubstWeakZero ; magic. }
          assert (
            eqterm G
                   (subst (subst u2 (sbweak G A2)) (sbzero G A2 u2))
                   u1
                   (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 u2))
          ).
          { eapply myEqTrans ; [ eassumption | magic .. ]. }
          assert (isterm G (subst (var 0) (sbzero G A2 u2)) A2).
          { eapply myTermTyConv ; [
              eapply myTermSubst ; magic
            | magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (var 0) (sbzero G A2 u2))
                   u2
                   (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 u2))
          ).
          { eapply myEqTyConv ; [
              eapply EqSubstZeroZero ; magic
            | try magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (var 0) (sbzero G A2 u2))
                   u1
                   (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 u2))
          ).
          { eapply myEqTrans ; [ eassumption | magic .. ]. }
          assert (
            eqtype G
                   (Subst (Id (Subst A2 (sbweak G A2))
                              (subst u2 (sbweak G A2))
                              (var 0)
                          )
                          (sbzero G A2 u2)
                   )
                   (Id A1 u1 u1)
          ).
          { gopushsubst. }
          assert (
            istype (ctxextend G (Id A1 u1 u1))
                   (Subst C1
                          (sbshift G
                                   (Id (Subst A1 (sbweak G A1))
                                       (subst u1 (sbweak G A1))
                                       (var 0)
                                   )
                                   (sbzero G A1 u1)
                          )
                   )
          ).
          { eapply myTySubst ; try magic.
            eapply mySubstCtxConv ; try magic.
            eapply CtxRefl ; magic.
          }
          assert (
            istype (ctxextend G (Id A1 u1 u1))
                   (Subst C2
                          (sbshift G
                                   (Id (Subst A2 (sbweak G A2))
                                       (subst u2 (sbweak G A2))
                                       (var 0)
                                   )
                                   (sbzero G A2 u2)
                          )
                   )
          ).
          { eapply myTySubst ; try magic.
            eapply mySubstCtxConv ; try magic.
            eapply CtxRefl ; magic.
          }
          assert (
            eqtype
              G
              (Subst
                 (Subst C1
                        (sbshift G
                                 (Id (Subst A1 (sbweak G A1))
                                     (subst u1 (sbweak G A1))
                                     (var 0)
                                 )
                                 (sbzero G A1 u1)
                        )
                 )
                 (sbzero G (Id A1 u1 u1) (refl A1 u1))
              )
              (Subst
                 (Subst C2
                        (sbshift G
                                 (Id (Subst A2 (sbweak G A2))
                                     (subst u2 (sbweak G A2))
                                     (var 0)
                                 )
                                 (sbzero G A2 u2)
                        )
                 )
                 (sbzero G (Id A2 u2 u2) (refl A2 u2))
              )
          ).
          { eapply myCongTySubst ; try magic ; try eassumption.
            - eapply myCongTySubst ; try magic.
              + eapply myEqSubstCtxConv ; [
                  eapply myCongSubstShift ; try magic
                | try magic ; try eassumption ..
                ].
                * apply CtxRefl ; magic.
                * eapply mySubstCtxConv ; magic.
              + eassumption.
              + eapply mySubstCtxConv ; magic.
              + eapply mySubstCtxConv ; magic.
            - eapply mySubstCtxConv ; magic.
          }
          assert (
            istype G
                   (Subst
                      (Subst C1
                             (sbshift G
                                      (Id (Subst A1 (sbweak G A1))
                                          (subst u1 (sbweak G A1))
                                          (var 0)
                                      )
                                      (sbzero G A1 u1)
                             )
                      )
                      (sbzero G (Id A1 u1 u1) (refl A1 u1))
                   )
          ).
          { eapply myTySubst ; try magic.
            eapply myTySubst ; try magic.
            eapply mySubstCtxConv ; try magic.
            eapply CtxRefl ; magic.
          }
          assert (
            eqtype G
                   (Subst
                      (Id (Subst A2 (sbweak G A2))
                          (subst u2 (sbweak G A2))
                          (var 0)
                      )
                      (sbzero G A2 u2)
                   )
                   (Id A2 u2 u2)
          ).
          { gopushsubst. }
          assert (
            istype G
                   (Subst
                      (Subst C2
                             (sbshift G
                                      (Id (Subst A2 (sbweak G A2))
                                          (subst u2 (sbweak G A2))
                                          (var 0)
                                      )
                                      (sbzero G A2 u2)
                             )
                      )
                      (sbzero G (Id A2 u2 u2) (refl A2 u2))
                   )
          ).
          { eapply myTySubst ; try magic.
            eapply myTySubst ; try magic.
            eapply mySubstCtxConv ; try magic.
            eapply CtxRefl ; magic.
          }
          assert (
            isterm
              G
              w2
              (Subst
                 (Subst
                    C2
                    (sbshift
                       G
                       (Id
                          (Subst A2 (sbweak G A2))
                          (subst u2 (sbweak G A2))
                          (var 0)
                       )
                       (sbzero G A2 u2))
                 )
                 (sbzero G (Id A2 u2 u2) (refl A2 u2))
              )
          ).
          { eapply myTermTyConv ; [ eassumption | try magic .. ].
            all:eassumption.
          }
          (* Some extra lemmata. *)
          assert (isterm G p1 (Id A2 u2 v2)).
          { eapply myTermTyConv ; [ eassumption | magic ..]. }
          assert (
            eqtype G A2 (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 v2))
          ).
          { apply EqTyWeakZero ; magic. }
          assert (
            eqtype G (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 v2)) A1
          ).
          { eapply myEqTyTrans ; [
              eapply myEqTySym ; [ eassumption | magic .. ]
            | magic ..
            ].
          }
          assert (
            isterm G u2 (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 v2))
          ).
          { eapply myTermTyConv ; [ exact i5 | magic .. ]. }
          assert (
            isterm G v2 (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 v2))
          ).
          { eapply myTermTyConv ; [ exact i7 | magic .. ]. }
          assert (
            eqterm G
                   (subst (subst u2 (sbweak G A2)) (sbzero G A2 v2))
                   u2
                   (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 v2))
          ).
          { eapply EqSubstWeakZero ; magic. }
          assert (isterm G (subst (var 0) (sbzero G A2 v2)) A2).
          { eapply myTermTyConv ; [
              eapply myTermSubst ; magic
            | magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (var 0) (sbzero G A2 v2))
                   v2
                   (Subst (Subst A2 (sbweak G A2)) (sbzero G A2 v2))
          ).
          { eapply myEqTyConv ; [
              eapply EqSubstZeroZero ; magic
            | magic ..
            ].
          }
          assert (eqterm G v1 v2 A2).
          { eapply myEqTyConv ; [ eassumption | magic .. ]. }
          assert (isterm G v1 A2).
          { eapply myTermTyConv ; [ eassumption | magic .. ]. }
          assert (eqterm G v2 v1 A2).
          { eapply myEqSym ; [ eassumption | magic .. ]. }
          assert (issubst (sbweak G A1) (ctxextend G A2) G).
          { eapply mySubstCtxConv ; magic. }
          assert (istype (ctxextend G A2) (Subst A1 (sbweak G A1))).
          { eapply myTySubst ; try magic ; try eassumption. }
          assert (eqsubst (sbweak G A1) (sbweak G A2) (ctxextend G A2) G).
          { eapply SubstSym ; try magic. }
          assert (
            isterm (ctxextend G A2)
                   (subst u1 (sbweak G A1))
                   (Subst A2 (sbweak G A2))
          ).
          { eapply myTermTyConv ; [
              eapply myTermSubst ; try magic ; try eassumption
            | try magic ; try eassumption ..
            ].
            eapply myCongTySubst ; try magic. eassumption.
          }
          assert (eqterm G u1 u2 A2).
          { eapply myEqTyConv ; [ exact H | magic .. ]. }
          assert (isterm G u1 A2).
          { eapply myTermTyConv ; [ exact i4 | magic .. ]. }
          assert (eqterm G u2 u1 A2).
          { eapply myEqSym ; [ eassumption | magic .. ]. }
          assert (
            isterm (ctxextend G A2) (var 0) (Subst A1 (sbweak G A1))
          ).
          { eapply myTermTyConv ; [
              eapply TermVarZero ; magic
            | magic ..
            ].
          }
          (* We can now proceed with the proof. *)
          eapply myTermTyConv ; [
            eapply TermJ ; try magic
          | try magic ..
          ].
          - eapply myCongTySubst ; try magic.
            + eapply myEqSubstCtxConv ; [
                eapply CongSubstZero ; try magic
              | try magic ..
              ].
              * eapply myEqSym ; [
                  eapply myEqTyConv ; [ eassumption | magic ..]
                | try magic ..
                ].
              * apply EqCtxExtend ; try magic. gopushsubst.
              * eapply mySubstCtxConv ; magic.
            + eapply myCongTySubst ; try magic.
              * { eapply myEqSubstCtxConv ; [
                    eapply myCongSubstShift ; try magic
                  | try magic ; try eassumption ..
                  ].
                  - apply CongId ; try magic.
                    (* Maybe enhance magic for this? *)
                    eapply myCongTermSubst ; try magic ; try eassumption.
                  - eapply mySubstCtxConv ; try magic.
                  - eapply mySubstCtxConv ; try magic.
                    eapply EqCtxExtend ; try magic.
                    admit.
                }
              * admit.
              * admit.
            + admit.
            + admit.
            + admit.
          - admit.
          - admit.
          Unshelve. all:admit.
        }
    }

  (* CongCond *)
  - { split.
      - { magic. }
      - { eapply myTermTyConv ; [
            eapply TermCond ; try magic
          | magic ..
          ].
          - eapply myTermTyConv ; [ eassumption | magic .. ].
          - eapply myTermTyConv ; [ eassumption | magic .. ].
        }
    }

  (* CongTermSubst *)
  - { split.
      - { magic. }
      - { eapply myTermTyConv ; [
            eapply myTermSubst ; try magic
          | magic ..
          ].
          eapply myTermTyConv ; [ eassumption | magic .. ].
          Unshelve. all:assumption.
    }

Admitted.

Theorem sane_eqterm G u v A :
  eqterm G u v A -> isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  intro H.
  destruct (sane_eqterm' G u v A H).
  auto using (@sane_isterm G u A).
Defined.

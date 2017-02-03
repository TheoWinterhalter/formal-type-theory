(* Sanity theorems for ptt. *)

Require Import syntax.
Require Import ptt.
Require Import ptt_tactics ptt_admissible.

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
    - now eapply SubstWeak.
    - assumption.
    - now apply (@CtxExtend G A).
    - eassumption.
  }

  (* TermVarSucc *)
  { apply (@TySubst (ctxextend G B) G).
    - now apply SubstWeak.
    - assumption.
    - now apply CtxExtend.
    - assumption.
  }

  (* TermAbs *)
  { now apply (@TyProd). }

  (* TermApp *)
  { apply (@TySubst G (ctxextend G A)).
    - now apply SubstZero.
    - assumption.
    - assumption.
    - now apply CtxExtend.
  }

  (* TermRefl *)
  { now apply TyId. }

  (* TermJ *)
  { trymagic. fail.



    apply @TySubst with (D := ctxextend G (Id A u v)) ; try magic.
    apply @TyCtxConv
      with (G :=
              ctxextend G
                        (Subst
                           (Id
                              (Subst A sbweak)
                              (subst u sbweak)
                              (var 0))
                           (sbzero v))).
    - eapply TySubst ; magic3.
    - apply EqCtxExtend ; try magic.
      assert (eqtype G A (Subst A (sbcomp sbweak (sbzero v)))).
      { eapply compWeakZero ; eassumption. }
      assert (eqtype G A (Subst (Subst A sbweak) (sbzero v))).
      { eapply EqTyWeakZero ; eassumption. }
      gopushsubst. apply CongId ; try magic.
      + eapply TermTyConv.
        * eassumption.
        * assumption.
        * assumption.
        * assumption.
        * magic.
      + eapply TermTyConv.
        * eassumption.
        * assumption.
        * assumption.
        * assumption.
        * magic.
      + { gocompsubst.
          - eapply EqTrans.
            + eapply CongTermSubst.
              * eapply WeakZero ; magic.
              * eapply EqRefl ; magic.
              * assumption.
              * assumption.
              * assumption.
              * assumption.
              * assumption.
              * magic.
              * magic.
            + eapply EqTyConv.
              * eapply EqIdSubst ; eassumption.
              * assumption.
              * assumption.
              * assumption.
              * magic.
              * { eapply TermTyConv.
                  - eapply TermSubst.
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
            + eapply TermTyConv.
              * eapply TermSubst ; try eassumption ; try magic.
              * eapply CongTySubst ; try eassumption ; try magic.
              * assumption.
              * magic.
              * magic.
            + eapply TermTyConv ; try eassumption ; try magic.
          - eapply TermTyConv.
            + eapply TermSubst.
              * magic.
              * eapply TermSubst ; try eassumption ; try magic.
              * assumption.
              * magic.
              * magic.
            + gocompsubst. Unshelve. all:assumption.
            + assumption.
            + magic.
            + magic.
          - eapply TermTyConv ; try eassumption ; try magic.
        }
      + eapply EqTyConv ; try eassumption ; try magic.
        eapply TermTyConv.
        * { eapply TermSubst.
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
    - magic3.
    - magic.
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
    + apply SubstZero.
      * assumption.
      * now apply TyBool.
      * assumption.
    + assumption.
    + assumption.
    + apply CtxExtend.
      * assumption.
      * now apply TyBool.
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
      + now apply SubstId.
      + assumption.
      + assumption.
      + eassumption.
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
        + apply (@TySubst _ (ctxextend D A)) ; auto.
          * now apply SubstShift.
          * apply CtxExtend ; auto.
            now apply (@TySubst G D).
          * now apply CtxExtend.
        + now apply (@TySubst G D).
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
      - magic.
      - magic.
    }

  (* CongSubstWeak *)
  - { split.
      - magic.
      - magic.
    }

  (* CongSubstShift *)
  - { split.
      - magic.
      - eapply SubstCtxConv ; magic.
        Unshelve. all:assumption.
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
        + { apply (@SubstCtxConv (ctxextend G (Subst (Subst A sbt) sbs)) _
                                 (ctxextend D (Subst A sbt))) ;
            auto using CtxExtend, (@TySubst D E), (@TySubst G D), (@TySubst G E),
                       (@SubstComp G D E), SubstShift, CtxRefl.
            apply EqCtxExtend ;
                auto using CtxRefl, (@TySubst G D), (@TySubst D E),
                           (@TySubst G E), (@SubstComp G D E).
              now apply (@EqTySubstComp G D E).
          }
        + apply CtxExtend ; auto.
          apply (@TySubst G E) ; auto using (@SubstComp G D E).
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
      - { apply (@TermTyConv G (Subst A (sbid' G)) A).
          - apply (@TermSubst G G) ; auto using SubstId.
          - now apply EqTyIdSubst.
          - assumption.
          - apply (@TySubst G G) ; auto using SubstId.
          - assumption.
        }
      - { assumption. }
    }

  (* EqSubstComp *)
  - { split.
      - { apply (@TermTyConv G (Subst (Subst A sbt) sbs) (Subst A (sbcomp sbt sbs))).
          - apply (@TermSubst G D) ; auto.
            + now apply (@TermSubst D E).
            + now apply (@TySubst D E).
          - now apply (@EqTySubstComp G D E).
          - assumption.
          - apply (@TySubst G D) ; auto.
            now apply (@TySubst D E).
          - apply (@TySubst G E) ; auto.
            now apply (@SubstComp G D E).
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
      - { eapply TermTyConv ; [
            eapply TermSubst ; magic
          | try magic ..
          ].
          eapply EqTySym ; try magic.
          eapply EqTyWeakZero ; magic.
          Unshelve. assumption.
        }
      - { assumption. }
    }

  (* EqSubstZeroSucc *)
  - { split.
      - { apply (@TermTyConv G (Subst (Subst A sbweak) (sbzero u))).
          - apply (@TermSubst G (ctxextend G B)) ; auto using CtxExtend.
            + now apply SubstZero.
            + now apply TermVarSucc.
            + apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
          - apply EqTySym ; try magic.
            eapply EqTyWeakZero ; magic.
          - assumption.
          - apply (@TySubst _ (ctxextend G B)) ; auto using CtxExtend, SubstZero.
            apply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
          - assumption.
          Unshelve. assumption.
        }
      - { assumption. }
    }

  (* EqSubstShiftZero *)
  - { split.
      - { eapply TermTyConv.
          - eapply TermSubst.
            + eapply SubstShift ; eassumption.
            + magic.
            + constructor.
              * assumption.
              * eapply TySubst ; eassumption.
            + eapply TySubst ; try eassumption ; magic.
            + magic.
          - eapply EqTyWeakNat ; magic.
          - constructor.
            + assumption.
            + eapply TySubst ; eassumption.
          - eapply TySubst.
            + eapply SubstShift ; eassumption.
            + eapply TySubst ; magic.
            + constructor.
              * assumption.
              * eapply TySubst ; eassumption.
            + magic.
          - eapply TySubst.
            + eapply SubstWeak.
              * eapply TySubst ; eassumption.
              * assumption.
            + eapply TySubst ; eassumption.
            + constructor. (* There may be room for maigc improvement here *)
              * assumption.
              * eapply TySubst ; eassumption.
            + magic.
        }
      - { magic. }
    }

  (* EqSubstShiftSucc *)
  - { split.
      - { eapply TermTyConv ; [
            (eapply TermSubst ; try magic) ;
            (eapply TermVarSucc ; try magic) ;
            eassumption
          | try magic ..
          ].
          eapply EqTyWeakNat ; magic.
          Unshelve. all:magic.
        }
      - { magic. }
    }

  (* EqSubstAbs *)
  - { split.
      - { eapply TermTyConv ; [
            eapply TermSubst ; magic
          | try magic ..
          ].
          gopushsubst.
        }
      - { magic. }
    }

  (* EqSubstApp *)
  - { split.
      - { magic. }
      - { eapply TermTyConv ; [
            (eapply TermApp ; try magic) ;
            (eapply TermTyConv ; [
              (eapply TermSubst ; try eassumption) ; magic
            | try magic ..
            ]) ;
            gopushsubst
          | try magic ..
          ].
          eapply EqTyShiftZero ; magic.
          Unshelve. all:magic.
        }
    }

  (* EqSubstRefl *)
  - { split.
      - { eapply TermTyConv ; [
            eapply TermSubst ; magic
          | try magic ..
          ].
          gopushsubst.
          Unshelve. all:assumption.
        }
      - { magic. }
    }

  (* EqSubstJ *)
  - { split.
      - { eapply TermSubst ; try magic.
          eapply TySubst ; try magic.
          eapply TySubst ; try magic.
          eapply SubstCtxConv ; try magic.
          - apply @EqCtxExtend
            with (A := Subst (Id (Subst A sbweak) (subst u sbweak) (var 0))
                            (sbzero v)
            ) ; try magic.
            gopushsubst.
            apply CongId ; try magic.
            + eapply TermTyConv ; [ eassumption | try magic .. ].
              eapply EqTyWeakZero ; magic.
            + eapply TermTyConv ; [ eassumption | try magic .. ].
              eapply EqTyWeakZero ; magic.
            + apply myEqTySym ; [
                eapply EqTyWeakZero ; magic
              | magic ..
              ].
            + eapply EqSubstWeakZero ; try magic.
              eapply TermTyConv ; [ eassumption | try magic .. ].
              eapply EqTyWeakZero ; magic.
            + eapply EqTyConv ; [
                eapply EqSubstZeroZero ; magic
              | try magic ..
              ].
              * eapply EqTyWeakZero ; magic.
              * eapply TermTyConv ; [
                  eapply TermSubst ; magic
                | try magic ..
                ].
                apply myEqTySym ; [
                  eapply EqTyWeakZero ; magic
                | magic ..
                ].
          - apply CtxRefl ; magic.
          Unshelve. all:magic.
        }
      - eapply JTyConv ; magic.
        Unshelve. assumption.
    }

  (* EqSubstExfalso *)
  - { split.
      - { magic. }
      - { eapply TermTyConv ; [
            apply TermExfalso ; try magic
          | try magic ..
          ].
          eapply TermTyConv ; [
            eapply TermSubst ; try magic
          | try magic ..
          ].
          gopushsubst.
          Unshelve. assumption.
        }
    }

  (* EqSubstUnit *)
  - { split.
      - { eapply TermTyConv ; [
            eapply TermSubst ; try magic
          | try magic ..
          ].
          gopushsubst.
        }
      - { magic. }
    }

  (* EqSubstTrue *)
  - { split.
      - { eapply TermTyConv ; [
            eapply TermSubst ; try magic
          | try magic ..
          ].
          gopushsubst.
        }
      - { magic. }
    }

  (* EqSubstFalse *)
  - { split.
      - { eapply TermTyConv ; [
            eapply TermSubst ; try magic
          | try magic ..
          ].
          gopushsubst.
        }
      - { magic. }
    }

  (* EqSubstCond *)
  - { split.
      - { magic. }
      - { eapply TermTyConv ; [
            apply TermCond ; try magic
          | try magic ..
          ].
          - eapply TermTyConv ; [
              eapply TermSubst ; try magic
            | try magic ..
            ].
            gopushsubst.
          - eapply TySubst ; try magic.
            eapply SubstCtxConv ; try magic.
            + apply EqCtxExtend ; try magic ; try gopushsubst.
            + apply CtxRefl ; magic.
          - eapply TermTyConv ; [
              eapply TermSubst ; try magic
            | try magic ..
            ].
            + eassumption.
            + apply EqTySym ; try magic.
              * eapply TySubst ; try magic.
                eapply TySubst ; try magic.
                { eapply SubstCtxConv ; try magic.
                  - apply EqCtxExtend ; try magic ; try gopushsubst.
                  - apply CtxRefl ; magic.
                }
              * { apply EqTySym ; try magic.
                  - eapply TySubst ; try magic.
                    eapply TySubst ; try magic.
                    eapply SubstCtxConv ; try magic.
                    + apply EqCtxExtend ; try magic ; try gopushsubst.
                    + apply CtxRefl ; magic.
                  - eapply EqTyTrans ; [
                      eapply myEqTySym ; [
                        eapply EqTyShiftZero ; magic
                      | magic ..
                      ]
                    | try magic ..
                    ].
                    + eapply CongTySubst ; try magic.
                      * { eapply CongSubstZero ; try magic.
                          - gopushsubst.
                          - gopushsubst.
                            + eapply TermTyConv ; [
                                eapply TermSubst ; magic
                              | try magic ; try gopushsubst ..
                              ].
                            + gopushsubst.
                            + eapply TermTyConv ; [
                                eapply TermSubst ; magic
                              | try magic ; try gopushsubst ..
                              ].
                          - eapply TermTyConv ; try magic.
                            gopushsubst.
                        }
                      * eapply SubstCtxConv ; try magic.
                        apply EqCtxExtend ; try magic.
                        gopushsubst.
                    + eapply TySubst ; try magic.
                      eapply TySubst ; try magic.
                      eapply SubstCtxConv ; try magic.
                      * apply EqCtxExtend ; try magic.
                        gopushsubst.
                      * apply CtxRefl ; magic.
                }
            + eapply TySubst ; try magic.
              eapply TySubst ; try magic.
              eapply SubstCtxConv ; try magic.
              * apply EqCtxExtend ; try magic.
                gopushsubst.
              * apply CtxRefl ; magic.
          - eapply TermTyConv ; [
              eapply TermSubst ; [ eassumption | eassumption | magic .. ]
            | try magic ..
            ].
            + { eapply EqTyTrans ; [
                  eapply myEqTySym ; [
                    eapply EqTyShiftZero ; magic
                  | magic ..
                  ]
                | try magic ..
                ].
                - eapply CongTySubst ; try magic.
                  + { eapply CongSubstZero ; try magic.
                      - gopushsubst.
                      - gopushsubst.
                        + eapply TermTyConv ; [
                            eapply TermSubst ; magic
                          | try magic ; try gopushsubst ..
                          ].
                        + gopushsubst.
                        + eapply TermTyConv ; [
                            eapply TermSubst ; magic
                          | try magic ; try gopushsubst ..
                          ].
                      - eapply TermTyConv ; try magic.
                        gopushsubst.
                    }
                  + eapply SubstCtxConv ; try magic.
                    apply EqCtxExtend ; try magic.
                    gopushsubst.
                - eapply TySubst ; try magic.
                  eapply TySubst ; try magic.
                  eapply SubstCtxConv ; try magic.
                  + apply EqCtxExtend ; try magic.
                    gopushsubst.
                  + apply CtxRefl ; magic.
              }
            + eapply TySubst ; try magic.
              eapply TySubst ; try magic.
              eapply SubstCtxConv ; try magic.
              * apply EqCtxExtend ; try magic. gopushsubst.
              * apply CtxRefl ; magic.
          - { apply EqTySym ; try magic.
              - eapply TySubst ; try magic.
                eapply SubstCtxConv ; try magic.
                + eapply SubstZero ; try magic.
                  eapply TermTyConv ; [
                    eapply TermSubst ; [ eassumption | eassumption | magic ..]
                    | try magic ..
                  ].
                  gopushsubst.
                + apply CtxRefl ; magic.
                + apply EqCtxExtend ; try magic ; try gopushsubst.
              - eapply EqTyTrans ; [
                  eapply myEqTySym ; [
                    eapply EqTyShiftZero ; magic
                  | magic ..
                  ]
                | try magic ..
                ].
                + eapply CongTySubst ; try magic.
                  * eapply CongSubstZero ; try magic.
                    gopushsubst.
                  * { eapply SubstCtxConv ; try magic.
                      - eapply SubstZero ; try magic.
                        eapply TermTyConv ; [
                          eapply TermSubst ;
                          [ eassumption | eassumption | magic ..]
                        | try magic ..
                        ].
                        gopushsubst.
                      - apply CtxRefl ; magic.
                      - apply EqCtxExtend ; try magic ; try gopushsubst.
                    }
                + eapply TySubst ; try magic.
                  eapply SubstCtxConv ; try magic.
                  * eapply SubstZero ; try magic.
                    eapply TermTyConv ; [
                      eapply TermSubst ; [ eassumption | eassumption | magic ..]
                    | try magic ..
                    ].
                    gopushsubst.
                  * apply CtxRefl ; magic.
                  * apply EqCtxExtend ; try magic ; try gopushsubst.
            }
          - eapply TySubst ; try magic.
            eapply SubstCtxConv ; try magic.
            * eapply SubstZero ; try magic.
              eapply TermTyConv ; [
                eapply TermSubst ; [ eassumption | eassumption | magic ..]
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
      - { eapply TermTyConv ; [
            eapply TermAbs ; try magic
          | magic ..
          ].
          eapply TermCtxConv ; [
            eapply TermTyConv ; [
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
      - { eapply TermTyConv ; [
            eapply TermApp ; try magic
          | try magic ..
          ].
          - eapply TermTyConv ; [
              eassumption
            | magic ..
            ].
          - eapply TermTyConv ; [
              eassumption
            | magic ..
            ].
          - eapply CongTySubst ; try magic.
            + eapply EqSubstCtxConv ; [
               eapply CongSubstZero ; try magic
              | try magic ..
              ].
              * eapply EqTyConv ; [
                  eapply EqSym ; try magic ; try eassumption
                | magic ..
                ].
              * eapply TermTyConv ; [
                  eassumption
                | magic ..
                ].
              * eapply TermTyConv ; [
                  eassumption
                | magic ..
                ].
              * eapply SubstZero ; try magic.
                eapply TermTyConv ; [
                  eassumption
                | magic ..
                ].
              * eapply SubstCtxConv ; magic.
            + magic.
            + eapply SubstCtxConv ; try magic.
              * eapply SubstZero ; try magic.
                eapply TermTyConv ; [
                  eassumption
                | magic ..
                ].
              * magic.
              * magic.
          - eapply TySubst.
            + eapply SubstZero ; try magic.
              eapply TermTyConv ; [
                eassumption
              | magic ..
              ].
            + magic.
            + magic.
            + magic.
        }
        Unshelve. all:magic.
        Unshelve. all:eapply TyCtxConv ; [ eassumption | magic .. ].
    }

  (* CongRefl *)
  - { split.
      - { magic. }
      - { eapply TermTyConv ; [
            eapply TermRefl ; try magic
          | try magic ..
          ].
          - eapply TermTyConv ; [ eassumption | magic .. ].
          - apply CongId ; try magic.
            + eapply TermTyConv ; [ eassumption | magic .. ].
            + eapply TermTyConv ; [ eassumption | magic .. ].
            + eapply TermTyConv ; [ eassumption | magic .. ].
            + eapply TermTyConv ; [ eassumption | magic .. ].
            + eapply EqTyConv ; [
                eapply myEqSym ; [ eassumption | magic .. ]
              | magic ..
              ].
            + eapply EqTyConv ; [
                eapply myEqSym ; [ eassumption | magic .. ]
              | magic ..
              ].
          - apply TyId ; try magic.
            + eapply TermTyConv ; [ eassumption | magic .. ].
            + eapply TermTyConv ; [ eassumption | magic .. ].
        }
    }

  (* CongJ *)
  - { split.
      - { eapply TermTyConv ; [
            eapply TermJ ; try magic
          | try magic ..
          ].
          - apply EqTyRefl ; try magic.
            eapply TySubst ; try magic.
            eapply TySubst ; try magic.
            eapply SubstCtxConv ; [
              eapply SubstShift ; magic
            | try magic ..
            ].
            + apply EqCtxExtend ; try magic.
              gopushsubst.
              eapply CongId ; try magic.
              * eapply TermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply TermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * apply myEqTySym ; try magic.
                apply EqTyWeakZero ; magic.
              * apply EqSubstWeakZero ; try magic.
                eapply TermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply EqTyConv ; [
                  eapply EqSubstZeroZero ; magic
                | try magic ..
                ].
                { apply EqTyWeakZero ; magic. }
                { eapply TermTyConv ; [
                    eapply TermSubst ; magic
                  | try magic ..
                  ].
                  apply myEqTySym ; try magic.
                  apply EqTyWeakZero ; magic.
                }
            + apply CtxRefl ; magic.
          - eapply TySubst ; try magic.
            eapply TySubst ; try magic.
            eapply SubstCtxConv ; [
              eapply SubstShift ; magic
            | try magic ..
            ].
            + apply EqCtxExtend ; try magic.
              gopushsubst.
              eapply CongId ; try magic.
              * eapply TermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply TermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * apply myEqTySym ; try magic.
                apply EqTyWeakZero ; magic.
              * apply EqSubstWeakZero ; try magic.
                eapply TermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply EqTyConv ; [
                  eapply EqSubstZeroZero ; magic
                | try magic ..
                ].
                { apply EqTyWeakZero ; magic. }
                { eapply TermTyConv ; [
                    eapply TermSubst ; magic
                  | try magic ..
                  ].
                  apply myEqTySym ; try magic.
                  apply EqTyWeakZero ; magic.
                }
            + apply CtxRefl ; magic.
          - eapply TySubst ; try magic.
            eapply TySubst ; try magic.
            eapply SubstCtxConv ; [
              eapply SubstShift ; magic
            | try magic ..
            ].
            + apply EqCtxExtend ; try magic.
              gopushsubst.
              eapply CongId ; try magic.
              * eapply TermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply TermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * apply myEqTySym ; try magic.
                apply EqTyWeakZero ; magic.
              * apply EqSubstWeakZero ; try magic.
                eapply TermTyConv ; [ eassumption | try magic .. ].
                apply EqTyWeakZero ; magic.
              * eapply EqTyConv ; [
                  eapply EqSubstZeroZero ; magic
                | try magic ..
                ].
                { apply EqTyWeakZero ; magic. }
                { eapply TermTyConv ; [
                    eapply TermSubst ; magic
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
          { eapply TermTyConv ; [ eassumption | magic .. ]. }
          assert (isterm G v2 A2).
          { eapply TermTyConv ; [ eassumption | magic .. ]. }
          assert (isterm G p2 (Id A2 u2 v2)).
          { eapply TermTyConv ; [ eassumption | magic .. ]. }
          assert (isterm G (refl A2 u2) (Id A1 u1 u1)).
          { eapply TermTyConv ; [ eapply TermRefl ; magic | magic .. ]. }
          assert (issubst (sbweak' G A2) (ctxextend G A1) G).
          { eapply SubstCtxConv ; magic. }
          assert (istype (ctxextend G A1) (Subst A2 (sbweak' G A2))).
          { eapply TySubst ; try magic ; try eassumption. }
          assert (eqsubst (sbweak' G A2) (sbweak' G A1) (ctxextend G A1) G).
          { eapply SubstSym ; try magic. }
          assert (
            eqtype (ctxextend G A1)
                   (Subst A2 (sbweak' G A2))
                   (Subst A1 (sbweak' G A1))
          ).
          { eapply CongTySubst ; try eassumption ; magic. }
          assert (
            isterm (ctxextend G A1)
                   (subst u2 (sbweak' G A2)) (Subst A1 (sbweak' G A1))
          ).
          { eapply TermTyConv ; [
              eapply TermSubst ; try magic ; try eassumption
            | try magic ; eassumption ..
            ].
          }
          assert (
            eqterm (ctxextend G A1)
                   (subst u1 (sbweak' G A1))
                   (subst u2 (sbweak' G A2))
                   (Subst A1 (sbweak' G A1))
          ).
          { eapply CongTermSubst ; magic. }
          assert (
            eqtype
              (ctxextend G A1)
              (Id (Subst A1 (sbweak' G A1)) (subst u1 (sbweak' G A1)) (var 0))
              (Id (Subst A2 (sbweak' G A2)) (subst u2 (sbweak' G A2)) (var 0))
          ).
          { eapply CongId ; try eassumption ; try magic. }
          assert (issubst (sbzero' G A2 u2) G (ctxextend G A1)).
          { eapply SubstCtxConv ; magic. }
          assert (isterm (ctxextend G A1) (var 0) (Subst A2 (sbweak' G A2))).
          { eapply TermTyConv ; [
              eapply TermVarZero ; magic
            | magic ..
            ].
          }
          assert (
            eqtype G A1 (Subst (Subst A1 (sbweak' G A1)) (sbzero' G A1 u1))
          ).
          { apply EqTyWeakZero ; magic. }
          assert (
            isterm G u1 (Subst (Subst A1 (sbweak' G A1)) (sbzero' G A1 u1))
          ).
          { eapply TermTyConv ; [ eassumption | magic .. ]. }
          assert (
            eqterm G
                   (subst (subst u1 (sbweak' G A1)) (sbzero' G A1 u1))
                   u1
                   (Subst (Subst A1 (sbweak' G A1)) (sbzero' G A1 u1))
          ).
          { eapply EqSubstWeakZero ; magic. }
          assert (isterm G (subst (var 0) (sbzero' G A1 u1)) A1).
          { eapply TermTyConv ; [
              eapply TermSubst ; magic
            | magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (var 0) (sbzero' G A1 u1))
                   u1
                   (Subst (Subst A1 (sbweak' G A1)) (sbzero' G A1 u1))
          ).
          { eapply EqTyConv ; [
              eapply EqSubstZeroZero ; magic
            | try magic ..
            ].
          }
          assert (
            eqtype G
                   (Subst (Id (Subst A1 (sbweak' G A1))
                              (subst u1 (sbweak' G A1))
                              (var 0)
                          )
                          (sbzero' G A1 u1)
                   )
                   (Id A1 u1 u1)
          ).
          { gopushsubst. }
          assert (
            eqtype G A2 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 u2))
          ).
          { apply EqTyWeakZero ; magic. }
          assert (
            eqtype G (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 u2)) A1
          ).
          { eapply EqTyTrans ; [
              eapply myEqTySym ; [ eassumption | magic .. ]
            | magic ..
            ].
          }
          assert (
            isterm G u1 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 u2))
          ).
          { eapply TermTyConv ; [ eassumption | magic .. ]. }
          assert (
            isterm G u2 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 u2))
          ).
          { eapply TermTyConv ; [ eassumption | magic .. ]. }
          assert (
            eqterm G u2 u1 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 u2))
          ).
          { eapply myEqSym ; [
              eapply EqTyConv ; [ eassumption | magic .. ]
            | magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (subst u2 (sbweak' G A2)) (sbzero' G A2 u2))
                   u2
                   (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 u2))
          ).
          { eapply EqSubstWeakZero ; magic. }
          assert (
            eqterm G
                   (subst (subst u2 (sbweak' G A2)) (sbzero' G A2 u2))
                   u1
                   (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 u2))
          ).
          { eapply EqTrans ; [ eassumption | magic .. ]. }
          assert (isterm G (subst (var 0) (sbzero' G A2 u2)) A2).
          { eapply TermTyConv ; [
              eapply TermSubst ; magic
            | magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (var 0) (sbzero' G A2 u2))
                   u2
                   (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 u2))
          ).
          { eapply EqTyConv ; [
              eapply EqSubstZeroZero ; magic
            | try magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (var 0) (sbzero' G A2 u2))
                   u1
                   (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 u2))
          ).
          { eapply EqTrans ; [ eassumption | magic .. ]. }
          assert (
            eqtype G
                   (Subst (Id (Subst A2 (sbweak' G A2))
                              (subst u2 (sbweak' G A2))
                              (var 0)
                          )
                          (sbzero' G A2 u2)
                   )
                   (Id A1 u1 u1)
          ).
          { gopushsubst. }
          assert (
            istype (ctxextend G (Id A1 u1 u1))
                   (Subst C1
                          (sbshift' G
                                   (Id (Subst A1 (sbweak' G A1))
                                       (subst u1 (sbweak' G A1))
                                       (var 0)
                                   )
                                   (sbzero' G A1 u1)
                          )
                   )
          ).
          { eapply TySubst ; try magic.
            eapply SubstCtxConv ; try magic.
            eapply CtxRefl ; magic.
          }
          assert (
            istype (ctxextend G (Id A1 u1 u1))
                   (Subst C2
                          (sbshift' G
                                   (Id (Subst A2 (sbweak' G A2))
                                       (subst u2 (sbweak' G A2))
                                       (var 0)
                                   )
                                   (sbzero' G A2 u2)
                          )
                   )
          ).
          { eapply TySubst ; try magic.
            eapply SubstCtxConv ; try magic.
            eapply CtxRefl ; magic.
          }
          assert (
            eqtype
              G
              (Subst
                 (Subst C1
                        (sbshift' G
                                 (Id (Subst A1 (sbweak' G A1))
                                     (subst u1 (sbweak' G A1))
                                     (var 0)
                                 )
                                 (sbzero' G A1 u1)
                        )
                 )
                 (sbzero' G (Id A1 u1 u1) (refl A1 u1))
              )
              (Subst
                 (Subst C2
                        (sbshift' G
                                 (Id (Subst A2 (sbweak' G A2))
                                     (subst u2 (sbweak' G A2))
                                     (var 0)
                                 )
                                 (sbzero' G A2 u2)
                        )
                 )
                 (sbzero' G (Id A2 u2 u2) (refl A2 u2))
              )
          ).
          { eapply CongTySubst ; try magic ; try eassumption.
            - eapply CongTySubst ; try magic.
              + eapply EqSubstCtxConv ; [
                  eapply CongSubstShift ; try magic
                | try magic ; try eassumption ..
                ].
                * apply CtxRefl ; magic.
                * eapply SubstCtxConv ; magic.
              + eassumption.
              + eapply SubstCtxConv ; magic.
              + eapply SubstCtxConv ; magic.
            - eapply SubstCtxConv ; magic.
          }
          assert (
            istype G
                   (Subst
                      (Subst C1
                             (sbshift' G
                                      (Id (Subst A1 (sbweak' G A1))
                                          (subst u1 (sbweak' G A1))
                                          (var 0)
                                      )
                                      (sbzero' G A1 u1)
                             )
                      )
                      (sbzero' G (Id A1 u1 u1) (refl A1 u1))
                   )
          ).
          { eapply TySubst ; try magic.
            eapply TySubst ; try magic.
            eapply SubstCtxConv ; try magic.
            eapply CtxRefl ; magic.
          }
          assert (
            eqtype G
                   (Subst
                      (Id (Subst A2 (sbweak' G A2))
                          (subst u2 (sbweak' G A2))
                          (var 0)
                      )
                      (sbzero' G A2 u2)
                   )
                   (Id A2 u2 u2)
          ).
          { gopushsubst. }
          assert (
            istype G
                   (Subst
                      (Subst C2
                             (sbshift' G
                                      (Id (Subst A2 (sbweak' G A2))
                                          (subst u2 (sbweak' G A2))
                                          (var 0)
                                      )
                                      (sbzero' G A2 u2)
                             )
                      )
                      (sbzero' G (Id A2 u2 u2) (refl A2 u2))
                   )
          ).
          { eapply TySubst ; try magic.
            eapply TySubst ; try magic.
            eapply SubstCtxConv ; try magic.
            eapply CtxRefl ; magic.
          }
          assert (
            isterm
              G
              w2
              (Subst
                 (Subst
                    C2
                    (sbshift'
                       G
                       (Id
                          (Subst A2 (sbweak' G A2))
                          (subst u2 (sbweak' G A2))
                          (var 0)
                       )
                       (sbzero' G A2 u2))
                 )
                 (sbzero' G (Id A2 u2 u2) (refl A2 u2))
              )
          ).
          { eapply TermTyConv ; [ eassumption | try magic .. ].
            all:eassumption.
          }
          (* Some extra lemmata. *)
          assert (isterm G p1 (Id A2 u2 v2)).
          { eapply TermTyConv ; [ eassumption | magic ..]. }
          assert (
            eqtype G A2 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { apply EqTyWeakZero ; magic. }
          assert (
            eqtype G (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2)) A1
          ).
          { eapply EqTyTrans ; [
              eapply myEqTySym ; [ eassumption | magic .. ]
            | magic ..
            ].
          }
          assert (
            isterm G u2 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { eapply TermTyConv ; [ exact i5 | magic .. ]. }
          assert (
            isterm G v2 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { eapply TermTyConv ; [ exact i7 | magic .. ]. }
          assert (
            eqterm G
                   (subst (subst u2 (sbweak' G A2)) (sbzero' G A2 v2))
                   u2
                   (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { eapply EqSubstWeakZero ; magic. }
          assert (isterm G (subst (var 0) (sbzero' G A2 v2)) A2).
          { eapply TermTyConv ; [
              eapply TermSubst ; magic
            | magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (var 0) (sbzero' G A2 v2))
                   v2
                   (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { eapply EqTyConv ; [
              eapply EqSubstZeroZero ; magic
            | magic ..
            ].
          }
          assert (eqterm G v1 v2 A2).
          { eapply EqTyConv ; [ eassumption | magic .. ]. }
          assert (isterm G v1 A2).
          { eapply TermTyConv ; [ eassumption | magic .. ]. }
          assert (eqterm G v2 v1 A2).
          { eapply myEqSym ; [ eassumption | magic .. ]. }
          assert (issubst (sbweak' G A1) (ctxextend G A2) G).
          { eapply SubstCtxConv ; magic. }
          assert (istype (ctxextend G A2) (Subst A1 (sbweak' G A1))).
          { eapply TySubst ; try magic ; try eassumption. }
          assert (eqsubst (sbweak' G A1) (sbweak' G A2) (ctxextend G A2) G).
          { eapply SubstSym ; try magic. }
          assert (
            isterm (ctxextend G A2)
                   (subst u1 (sbweak' G A1))
                   (Subst A2 (sbweak' G A2))
          ).
          { eapply TermTyConv ; [
              eapply TermSubst ; try magic ; try eassumption
            | try magic ; try eassumption ..
            ].
            eapply CongTySubst ; try magic. eassumption.
          }
          assert (eqterm G u1 u2 A2).
          { eapply EqTyConv ; [ exact H | magic .. ]. }
          assert (isterm G u1 A2).
          { eapply TermTyConv ; [ exact i4 | magic .. ]. }
          assert (eqterm G u2 u1 A2).
          { eapply myEqSym ; [ eassumption | magic .. ]. }
          assert (
            isterm (ctxextend G A2) (var 0) (Subst A1 (sbweak' G A1))
          ).
          { eapply TermTyConv ; [
              eapply TermVarZero ; magic
            | magic ..
            ].
          }
          assert (issubst (sbzero' G A2 v2) G (ctxextend G A1)).
          { eapply SubstCtxConv ; magic. }
          assert (
            isterm G u1 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { eapply TermTyConv ; [ eassumption | magic .. ]. }
          assert (
            isterm G v1 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { eapply TermTyConv ; [ eassumption | magic .. ]. }
          assert (
            eqterm G u2 u1 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { eapply EqTyConv ; [ eassumption | magic .. ]. }
          assert (
            eqterm G
                   (subst (subst u2 (sbweak' G A2)) (sbzero' G A2 v2))
                   u1
                   (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { eapply @EqTrans with (v:=u2) ; magic. }
          assert (
            eqterm G v2 v1 (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { eapply EqTyConv ; [ eassumption | magic .. ]. }
          assert (
            eqterm G
                   (subst (var 0) (sbzero' G A2 v2))
                   v1
                   (Subst (Subst A2 (sbweak' G A2)) (sbzero' G A2 v2))
          ).
          { eapply @EqTrans with (v:=v2) ; magic. }
          assert (
            eqtype G A1 (Subst (Subst A1 (sbweak' G A1)) (sbzero' G A1 v1))
          ).
          { apply EqTyWeakZero ; magic. }
          assert (
            isterm G u1 (Subst (Subst A1 (sbweak' G A1)) (sbzero' G A1 v1))
          ).
          { eapply TermTyConv ; [ exact i4 | magic .. ]. }
          assert (
            isterm G v1 (Subst (Subst A1 (sbweak' G A1)) (sbzero' G A1 v1))
          ).
          { eapply TermTyConv ; [ exact i6 | magic .. ]. }
          assert (
            eqterm G
                   (subst (subst u1 (sbweak' G A1)) (sbzero' G A1 v1))
                   u1
                   (Subst (Subst A1 (sbweak' G A1)) (sbzero' G A1 v1))
          ).
          { eapply EqSubstWeakZero ; magic. }
          assert (isterm G (subst (var 0) (sbzero' G A1 v1)) A1).
          { eapply TermTyConv ; [
              eapply TermSubst ; magic
            | magic ..
            ].
          }
          assert (
            eqterm G
                   (subst (var 0) (sbzero' G A1 v1))
                   v1
                   (Subst (Subst A1 (sbweak' G A1)) (sbzero' G A1 v1))
          ).
          { eapply EqTyConv ; [
              eapply EqSubstZeroZero ; magic
            | magic ..
            ].
          }
          (* We can now proceed with the proof. *)
          eapply TermTyConv ; [
            eapply TermJ ; try magic
          | try magic ..
          ].
          - eapply CongTySubst ; try magic.
            + eapply EqSubstCtxConv ; [
                eapply CongSubstZero ; try magic
              | try magic ..
              ].
              * eapply myEqSym ; [
                  eapply EqTyConv ; [ eassumption | magic ..]
                | try magic ..
                ].
              * apply EqCtxExtend ; try magic. gopushsubst.
              * eapply SubstCtxConv ; magic.
            + eapply CongTySubst ; try magic.
              * { eapply EqSubstCtxConv ; [
                    eapply CongSubstShift ; try magic
                  | try magic ; try eassumption ..
                  ].
                  - eapply SubstCtxConv ; magic.
                  - eapply SubstCtxConv ; magic.
                }
              * eapply EqTyCtxConv ; [
                  eapply myEqTySym ; [ eassumption | magic .. ]
                | magic ..
                ].
              * eapply SubstCtxConv ; magic.
            + eapply TyCtxConv ; [
                eapply TySubst ; magic
              | magic ..
              ].
            + eapply SubstCtxConv ; try magic.
              apply EqCtxExtend ; try magic. gopushsubst.
            + eapply SubstCtxConv ; try magic.
              apply EqCtxExtend ; try magic. gopushsubst.
          - eapply TySubst ; try magic.
            eapply TySubst ; try magic.
            eapply SubstCtxConv ; try magic.
            + apply EqCtxExtend ; try magic. gopushsubst.
            + apply CtxRefl ; magic.
          - eapply TySubst ; try magic.
            eapply TySubst ; try magic.
            eapply SubstCtxConv ; try magic.
            + apply EqCtxExtend ; try magic. gopushsubst.
            + apply CtxRefl ; magic.
          Unshelve. all:magic.
          Unshelve.
          all:eapply TyCtxConv ; [ eassumption | magic .. ].
        }
    }

  (* CongCond *)
  - { split.
      - { magic. }
      - { eapply TermTyConv ; [
            eapply TermCond ; try magic
          | magic ..
          ].
          - eapply TermTyConv ; [ eassumption | magic .. ].
          - eapply TermTyConv ; [ eassumption | magic .. ].
        }
    }

  (* CongTermSubst *)
  - { split.
      - { magic. }
      - { eapply TermTyConv ; [
            eapply TermSubst ; try magic
          | magic ..
          ].
          eapply TermTyConv ; [ eassumption | magic .. ].
          Unshelve. all:assumption.
        }
    }

Defined.

Theorem sane_eqterm G u v A :
  eqterm G u v A -> isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  intro H.
  destruct (sane_eqterm' G u v A H).
  auto using (@sane_isterm G u A).
Defined.

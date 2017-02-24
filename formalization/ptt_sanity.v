(* Sanity theorems for ptt. *)

Require Import syntax.
Require Import ptt.
Require Import config_tactics ptt_tactics ptt_admissible.
Require tt.

Definition sane_issubst sbs G D :
  issubst sbs G D -> isctx G * isctx D.
Proof.
  intro H ; destruct H ; doConfig.

  (* SubstZero *)
  { split.

    - assumption.
    - now capply CtxExtend.
  }

  (* SubstWeak *)
  { split.

    - now capply CtxExtend.
    - assumption.
  }

  (* SubstShift *)
  { split.

    - capply CtxExtend.
      + assumption.
      + now capply (@TySubst G D).
    - now capply CtxExtend.
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
  intro H; destruct H ; config assumption.
Defined.

Definition sane_isterm' G u A :
  isterm G u A -> istype G A.
Proof.
  intro H ; destruct H.

  (* TermTyConv *)
  { config assumption. }

  (* TermCtxConv *)
  { now capply (@TyCtxConv G D). }

  (* TermSubst *)
  { now capply (@TySubst G D A sbs). }

  (* TermVarZero *)
  { ceapply TySubst.
    - now ceapply SubstWeak.
    - assumption.
    - now capply (@CtxExtend G A).
    - eassumption.
  }

  (* TermVarSucc *)
  { capply (@TySubst (ctxextend G B) G).
    - now capply SubstWeak.
    - assumption.
    - now capply CtxExtend.
    - assumption.
  }

  (* TermAbs *)
  { now capply (@TyProd). }

  (* TermApp *)
  { capply (@TySubst G (ctxextend G A)).
    - now capply SubstZero.
    - assumption.
    - assumption.
    - now capply CtxExtend.
  }

  (* TermRefl *)
  { now capply TyId. }

  (* TermJ *)
  { magic. Unshelve. all:strictmagic. }

  (* TermExfalso *)
  { assumption. }

  (* TermUnit *)
  { now capply TyUnit. }

  (* TermTrue *)
  { now capply TyBool. }

  (* TermFalse *)
  { now capply TyBool. }

  (* TermCond *)
  { ceapply (@TySubst G (ctxextend G Bool)).
    + config capply SubstZero.
      * assumption.
      * now capply TyBool.
      * assumption.
    + assumption.
    + assumption.
    + capply CtxExtend.
      * assumption.
      * now capply TyBool.
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
  intro H ; destruct H ; doConfig.

  (* EqTyCtxConv *)
  { split.
    - { now capply (@TyCtxConv G D). }
    - { now capply (@TyCtxConv G D). }
  }

  (* EqTyRefl*)
  { split ; assumption. }

  (* EqTySym *)
  { split ; assumption. }

  (* EqTyTrans *)
  { split ; assumption. }

  (* EqTyIdSubst *)
  { split.
    - ceapply TySubst.
      + now capply SubstId.
      + assumption.
      + assumption.
      + eassumption.
    - assumption.
  }

  (* EqTySubstComp *)
  { split.
    - capply (@TySubst G D) ; auto.
      capply (@TySubst D E) ; auto.
    - capply (@TySubst G E) ; auto.
      capply (@SubstComp G D E) ; auto.
  }

  (* EqTySubstProd *)
  { split.
    - { capply (@TySubst G D) ; auto using TyProd. }
    - { capply TyProd ; auto.
        + capply (@TySubst _ (ctxextend D A)) ; auto.
          * now capply SubstShift.
          * capply CtxExtend ; auto.
            now capply (@TySubst G D).
          * now capply CtxExtend.
        + now capply (@TySubst G D).
      }
  }

  (* EqTySubstId *)
  { split.
    - { capply (@TySubst G D) ; auto using TyId. }
    - { capply TyId ; auto using (@TySubst G D), (@TermSubst G D). }
  }

  (* EqTySubstEmpty *)
  { split.
    - { capply (@TySubst G D) ; auto using TyEmpty. }
    - { now capply TyEmpty. }
  }

  (* EqTySubstUnit *)
  { split.
    - { capply (@TySubst G D) ; auto using TyUnit. }
    - { now capply TyUnit. }
  }

  (* EqTySubstBool *)
  { split.
    - { capply (@TySubst G D) ; auto using TyBool. }
    - { now capply TyBool. }
  }

  (* EqTyExfalso *)
  { split ; assumption. }

  (* CongProd *)
  { split.
    - { now capply TyProd. }
    - { capply TyProd ; auto.
        capply (@TyCtxConv (ctxextend G A1)) ; auto using CtxExtend.
        capply EqCtxExtend ; auto using CtxRefl.
      }
  }

  (* CongId *)
  { split.
    - { now capply TyId. }
    - { capply TyId.
        - assumption.
        - assumption.
        - now capply (@TermTyConv G A B v1).
        - now capply (@TermTyConv G A B v2).
      }
  }

  (* CongTySubst *)
  { split.
    - { now capply (@TySubst G D). }
    - { now capply (@TySubst G D). }
  }

Defined.

Theorem sane_eqctx G D :
  eqctx G D -> isctx G * isctx D.
Proof.
  intro H ; destruct H ; doConfig.

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
    - now capply CtxEmpty.
    - now capply CtxEmpty.
  }

  (* EqCtxExtend *)
  { split.
    - now capply CtxExtend.
    - capply CtxExtend.
      + assumption.
      + capply (@TyCtxConv G D) ; auto.
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
  intro H ; destruct H ; doConfig.

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
      - now capply SubstZero.
      - capply (@SubstCtxConv G G (ctxextend G A2) (ctxextend G A1)) ;
          auto using CtxExtend, CtxRefl, CtxSym.
        + capply SubstZero ;
            auto using (@TyCtxConv G G), (@TermCtxConv G G), (@TermTyConv G A1 A2).
        + capply EqCtxExtend ;
            auto using (@TyCtxConv G G), CtxRefl, (@EqTyCtxConv G G), EqTySym.
    }

  (* CongSubstWeak *)
  - { split ; magic. }

  (* CongSubstShift *)
  - { split ; magic. }

  (* CongSubstComp *)
  - { split.
      - now capply (@SubstComp G D E).
      - now capply (@SubstComp G D E).
    }

  (* EqSubstCtxConv *)
  - { split.
      - now capply (@SubstCtxConv G1 G2 D1 D2).
      - now capply (@SubstCtxConv G1 G2 D1 D2).
    }

  (* CompAssoc *)
  - { split.
      - capply (@SubstComp G E F) ; auto.
        now capply (@SubstComp G D E).
      - capply (@SubstComp G D F); auto.
        now capply (@SubstComp D E F).
    }

  (* WeakNat *)
  - { split.
      - capply (@SubstComp _ (ctxextend D A)) ;
          auto using CtxExtend, (@TySubst G D), SubstShift, SubstWeak.
      - capply (@SubstComp _ G) ;
          auto using CtxExtend, (@TySubst G D), SubstWeak.
    }

  (* WeakZero *)
  - { split.
      - capply (@SubstComp _ (ctxextend G A)) ;
          auto using CtxExtend, SubstZero, SubstWeak.
      - now capply SubstId.
    }

  (* ShiftZero *)
  - { split.
      - capply (@SubstComp _ (ctxextend G (Subst A sbs))) ;
          auto using CtxExtend, (@TySubst G D), SubstZero, (@TermSubst G D), SubstShift.
      - capply (@SubstComp _ D) ;
          auto using CtxExtend, SubstZero.
    }

  (* CompShift *)
  - { split.
      - capply (@SubstComp _ (ctxextend D (Subst A sbt))) ;
          auto using CtxExtend, (@TySubst D E), SubstShift.
        + { capply (@SubstCtxConv (ctxextend G (Subst (Subst A sbt) sbs)) _
                                 (ctxextend D (Subst A sbt))) ;
            auto using CtxExtend, (@TySubst D E), (@TySubst G D), (@TySubst G E),
                       (@SubstComp G D E), SubstShift, CtxRefl.
            capply EqCtxExtend ;
                auto using CtxRefl, (@TySubst G D), (@TySubst D E),
                           (@TySubst G E), (@SubstComp G D E).
              now capply (@EqTySubstComp G D E).
          }
        + capply CtxExtend ; auto.
          capply (@TySubst G E) ; auto using (@SubstComp G D E).
      - capply SubstShift ; auto using (@SubstComp G D E).
    }

  (* CompIdRight *)
  - { split.
      - capply (@SubstComp G G D) ; auto using SubstId.
      - assumption.
    }

  (* CompIdLeft *)
  - { split.
      - capply (@SubstComp G D D) ; auto using SubstId.
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
  intro H ; destruct H ; doConfig.

  (* EqTyConv *)
  - { split.
      - { now capply (@TermTyConv G A B u). }
      - { now capply (@TermTyConv G A B v). }
    }

  (* EqCtxConv *)
  - { split.
      - { now capply (@TermCtxConv G D A). }
      - { now capply (@TermCtxConv G D A). }
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
      - { capply (@TermTyConv G (Subst A sbid) A).
          - capply (@TermSubst G G) ; auto using SubstId.
          - now capply EqTyIdSubst.
          - assumption.
          - capply (@TySubst G G) ; auto using SubstId.
          - assumption.
        }
      - { assumption. }
    }

  (* EqSubstComp *)
  - { split.
      - { capply (@TermTyConv G (Subst (Subst A sbt) sbs) (Subst A (sbcomp sbt sbs))).
          - capply (@TermSubst G D) ; auto.
            + now capply (@TermSubst D E).
            + now capply (@TySubst D E).
          - now capply (@EqTySubstComp G D E).
          - assumption.
          - capply (@TySubst G D) ; auto.
            now capply (@TySubst D E).
          - capply (@TySubst G E) ; auto.
            now capply (@SubstComp G D E).
        }
      - { capply (@TermSubst G E) ; auto.
          now capply (@SubstComp G D E).
        }
    }

  (* EqSubstWeak *)
  - { split.
      - { capply (@TermSubst _ G) ; auto using CtxExtend.
          now capply SubstWeak.
        }
      - { now capply TermVarSucc. }
    }


  (* EqSubstZeroZero *)
  - { split.
      - { capply (@TermTyConv G (Subst (Subst A (sbweak A)) (sbzero A u))).
          - capply (@TermSubst _ (ctxextend G A)) ; auto using CtxExtend.
            + now capply SubstZero.
            + now capply TermVarZero.
            + capply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
          - capply (@EqTyTrans G _ (Subst A sbid)) ; auto.
            + { capply (@EqTyTrans _ _ (Subst A (sbcomp (sbweak A) (sbzero A u)))) ; auto.
                - capply (@EqTySubstComp G (ctxextend G A) G) ;
                    auto using CtxExtend, (@SubstComp G (ctxextend G A)) , SubstWeak, SubstZero.
                - capply (@CongTySubst G G) ;
                    auto using CtxExtend, (@SubstComp G (ctxextend G A)) , SubstWeak, SubstZero, SubstId, EqTyRefl, WeakZero.
                - capply (@TySubst _ (ctxextend G A)) ; auto using CtxExtend, SubstZero.
                  capply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
                - capply (@TySubst _ G) ; auto.
                  + capply (@SubstComp _ (ctxextend G A)) ; auto using CtxExtend, SubstWeak, SubstZero.
                - capply (@TySubst _ G) ; auto using SubstId.
              }
            + now capply EqTyIdSubst.
            + capply (@TySubst _ (ctxextend G A)) ; auto using CtxExtend.
              * now capply SubstZero.
              * capply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
            + capply (@TySubst _ G) ; auto using SubstId.
          - assumption.
          - capply (@TySubst _ (ctxextend G A)) ; auto using CtxExtend.
            + now capply SubstZero.
            + capply (@TySubst _ G) ; auto using CtxExtend.
              now capply SubstWeak.
          - assumption.
        }
      - { assumption. }
    }

  (* EqSubstZeroSucc *)
  - { split.
      - { capply (@TermTyConv G (Subst (Subst A (sbweak B)) (sbzero B u))).
          - capply (@TermSubst G (ctxextend G B)) ; auto using CtxExtend.
            + now capply SubstZero.
            + now capply TermVarSucc.
            + capply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
          - capply EqTySym ; magic.
          - assumption.
          - capply (@TySubst _ (ctxextend G B)) ; auto using CtxExtend, SubstZero.
            capply (@TySubst _ G) ; auto using CtxExtend, SubstWeak.
          - assumption.
        }
      - { assumption. }
    }

  (* EqSubstShiftZero *)
  - { split.
      - { ceapply TermTyConv.
          - ceapply TermSubst.
            + ceapply SubstShift ; eassumption.
            + magic.
            + config constructor.
              * assumption.
              * ceapply TySubst ; eassumption.
            + ceapply TySubst ; try eassumption ; magic.
            + magic.
          - magic.
          - config constructor.
            + assumption.
            + ceapply TySubst ; eassumption.
          - ceapply TySubst.
            + ceapply SubstShift ; eassumption.
            + ceapply TySubst ; magic.
            + config constructor.
              * assumption.
              * ceapply TySubst ; eassumption.
            + magic.
          - ceapply TySubst.
            + ceapply SubstWeak.
              * ceapply TySubst ; eassumption.
              * assumption.
            + ceapply TySubst ; eassumption.
            + config constructor. (* There may be room for maigc improvement here *)
              * assumption.
              * ceapply TySubst ; eassumption.
            + magic.
        }
      - { magic. }
    }

  (* EqSubstShiftSucc *)
  - { split.
      - { magic. Unshelve. all:strictmagic. }
      - { magic. }
    }

  (* EqSubstAbs *)
  - { split.
      - { magic. Unshelve. all:strictmagic. }
      - { magic. }
    }

  (* EqSubstApp *)
  - { split.
      - { magic. }
      - { magic. Unshelve. all:strictmagic. }
    }

  (* EqSubstRefl *)
  - { split.
      - { magic. Unshelve. all:strictmagic. }
      - { magic. }
    }

  (* EqSubstJ *)
  - { split.
      - { magic. Unshelve. all:strictmagic. }
      - { (* magic. *) admit.
        }
    }

  (* EqSubstExfalso *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstUnit *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstTrue *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstFalse *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* EqSubstCond *)
  - { split.
      - { magic. }
      - { admit. }
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
      - { magic. }
    }

  (* CongApp *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongRefl *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongJ *)
  - { split.
      - { magic. }
      - { admit. }
    }

  (* CongCond *)
  - { split.
      - { magic. }
      - { magic. }
    }

  (* CongTermSubst *)
  - { split.
      - { magic. }
      - { magic. }
    }

Admitted.

Theorem sane_eqterm G u v A :
  eqterm G u v A -> isctx G * istype G A * isterm G u A * isterm G v A.
Proof.
  intro H.
  destruct (sane_eqterm' G u v A H).
  auto using (@sane_isterm G u A).
Defined.

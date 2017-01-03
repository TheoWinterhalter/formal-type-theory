Require Import syntax.
Require ett ptt.

Axiom postpone_proof : forall A : Type, A.
Ltac later := apply postpone_proof.

Fixpoint sane_isctx G (P : ett.isctx G) {struct P} : ptt.isctx G

with sane_issubst sbs G D (P : ett.issubst sbs G D) {struct P} : ptt.issubst sbs G D

with sane_istype G A (P : ett.istype G A) {struct P} : ptt.istype G A

with sane_isterm G u A (P : ett.isterm G u A) {struct P} : ptt.isterm G u A

with sane_eqsubst sbs sbt G D (P : ett.eqsubst sbs sbt G D) {struct P} : ptt.eqsubst sbs sbt G D

with sane_eqctx G D (P : ett.eqctx G D) {struct P} : ptt.eqctx G D

with sane_eqtype G A B (P : ett.eqtype G A B) {struct P} : ptt.eqtype G A B

with sane_eqterm G u v A (P : ett.eqterm G u v A) {struct P} : ptt.eqterm G u v A.

Proof.

  (* sane_isctx *)
  { destruct P.

    (* CtxEmpty *)
    - { apply ptt.CtxEmpty. }

    (* CtxExtend *)
    - {
        intros ; apply ptt.CtxExtend.
        + now apply sane_isctx.
        + now apply sane_istype.
      }
  }

  (* sane_issubst *)
  { destruct P.

    (* SubstZero *)
    - { apply ptt.SubstZero.
        + eapply ptt.sane_isterm.
          eapply sane_isterm ; eassumption.
        + eapply ptt.sane_isterm.
          eapply sane_isterm ; eassumption.
        + now apply sane_isterm.
      }

    (* SubstWeak *)
    - {
        apply ptt.SubstWeak.
        + eapply ptt.sane_istype.
          eapply sane_istype ; eassumption.
        + now apply sane_istype.
      }

    (* SubstShift. *)
    - {
        apply ptt.SubstShift.
        + eapply (ptt.sane_issubst sbs G D).
          now apply sane_issubst.
        + eapply (ptt.sane_istype D A).
          now apply sane_istype.
        + now apply sane_issubst.
        + now apply sane_istype.
      }

     (* SubstId *)
     - {
         apply ptt.SubstId.
         - now apply sane_isctx.
       }

     (* SubstComp *)
     - {
         apply (@ptt.SubstComp G D E).
         - apply (ptt.sane_issubst sbs G D).
           now apply sane_issubst.
         - apply (ptt.sane_issubst sbt D E).
           now apply sane_issubst.
         - apply (ptt.sane_issubst sbt D E).
           now apply sane_issubst.
         - now apply sane_issubst.
         - now apply sane_issubst.
       }

     (* SubstCtxConv *)
     - {
         apply (@ptt.SubstCtxConv G1 G2 D1 D2).
         - apply (ptt.sane_eqctx G1 G2).
           now apply sane_eqctx.
         - apply (ptt.sane_eqctx G1 G2).
           now apply sane_eqctx.
         - apply (ptt.sane_eqctx D1 D2).
           now apply sane_eqctx.
         - apply (ptt.sane_eqctx D1 D2).
           now apply sane_eqctx.
         - now apply sane_issubst.
         - now apply sane_eqctx.
         - now apply sane_eqctx.
       }
  }

  (* sane_istype *)
  { destruct P.

    (* TyCtxConv *)
    { apply (@ptt.TyCtxConv G D).
      - now apply (ptt.sane_eqctx G D), sane_eqctx.
      - now apply (ptt.sane_eqctx G D), sane_eqctx.
      - now apply sane_istype.
      - now apply sane_eqctx.
    }

    (* TySubst *)
    { apply (@ptt.TySubst G D).
      - now apply (ptt.sane_issubst sbs G D), sane_issubst.
      - now apply (ptt.sane_istype D A), sane_istype.
      - now apply sane_issubst.
      - now apply sane_istype.
    }

    (* TyProd *)
    { apply ptt.TyProd.
      - now apply (ptt.sane_istype G A), sane_istype.
      - now apply sane_istype.
      - now apply sane_istype.
    }

    (* TyId *)
    { apply ptt.TyId.
      - now apply (ptt.sane_istype G A), sane_istype.
      - now apply sane_istype.
      - now apply sane_isterm.
      - now apply sane_isterm.
    }

    (* TyEmpty *)
    { apply ptt.TyEmpty.
      - now apply sane_isctx.
    }

    (* TyUnit *)
    { apply ptt.TyUnit.
      - now apply sane_isctx.
    }

    (* TyBool *)
    { apply ptt.TyBool.
      - now apply sane_isctx.
    }
  }

  (* sane_isterm *)
  {
    later.
  }

  (* sane_eqsubst *)
  {
    later.
  }

  (* sane_eqctx *)
  {
    later.
  }

  (* sane_eqtype *)
  {
    later.
  }

  (* sane_eqterm *)
  {
    later.
  }

Defined.
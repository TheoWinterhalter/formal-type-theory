(* Elaborating Annotations

   We propose a translation from concise syntax to annotated syntax.
   For this purpose, we have to rely on a typing derivation to retrieve
   the missing annotations.
 *)

Require config.
Require Import config_tactics.

Require syntax.
Require Import tt.
Require annotated_syntax concise_syntax.
Require Import forget_annotation.

(* Concise theory *)
Module Ctt.

  Section Ctt.

    Local Instance havePrecondition : config.Precondition :=
      {| config.flagPrecondition := config.Yes |}.
    Context `{configReflection : config.Reflection}.
    Context `{configBinaryProdType : config.BinaryProdType}.
    Context `{configProdEta : config.ProdEta}.
    Context `{configUniverses : config.Universes}.
    Context `{configPropType : config.PropType}.
    Context `{configIdType : config.IdType}.
    Context `{configIdEliminator : config.IdEliminator}.
    Context `{configEmptyType : config.EmptyType}.
    Context `{configUnitType : config.UnitType}.
    Context `{configBoolType : config.BoolType}.
    Context `{configProdType : config.ProdType}.

    Local Existing Instance concise_syntax.Syntax.

    Definition isctx   := isctx.
    Definition issubst := issubst.
    Definition istype  := istype.
    Definition isterm  := isterm.
    Definition eqctx   := eqctx.
    Definition eqsubst := eqsubst.
    Definition eqtype  := eqtype.
    Definition eqterm  := eqterm.

  End Ctt.

End Ctt.

Module C := concise_syntax.

(* Annotated theory *)
Module Att.

  Section Att.

    Local Instance noPrecondition : config.Precondition :=
      {| config.flagPrecondition := config.No |}.
    Context `{configReflection : config.Reflection}.
    Context `{configBinaryProdType : config.BinaryProdType}.
    Context `{configProdEta : config.ProdEta}.
    Context `{configUniverses : config.Universes}.
    Context `{configPropType : config.PropType}.
    Context `{configIdType : config.IdType}.
    Context `{configIdEliminator : config.IdEliminator}.
    Context `{configEmptyType : config.EmptyType}.
    Context `{configUnitType : config.UnitType}.
    Context `{configBoolType : config.BoolType}.
    Context `{configProdType : config.ProdType}.

    Local Existing Instance annotated_syntax.Syntax.

    Definition isctx   := isctx.
    Definition issubst := issubst.
    Definition istype  := istype.
    Definition isterm  := isterm.
    Definition eqctx   := eqctx.
    Definition eqsubst := eqsubst.
    Definition eqtype  := eqtype.
    Definition eqterm  := eqterm.

  End Att.

End Att.

Module A := annotated_syntax.

Section Translation.

Context `{configReflection : config.Reflection}.
Context `{configBinaryProdType : config.BinaryProdType}.
Context `{configProdEta : config.ProdEta}.
Context `{configUniverses : config.Universes}.
Context `{configPropType : config.PropType}.
Context `{configIdType : config.IdType}.
Context `{configIdEliminator : config.IdEliminator}.
Context `{configEmptyType : config.EmptyType}.
Context `{configUnitType : config.UnitType}.
Context `{configBoolType : config.BoolType}.
Context `{configProdType : config.ProdType}.

Open Scope type_scope.

(* Notion of elaborations *)
Record context_elab (G : C.context) := {
  ctx : A.context ;
  eqctx : forget_ctx ctx = G ;
  isctx : Att.isctx ctx
}.

Arguments ctx {_} _.
Arguments eqctx {_} _.
Arguments isctx {_} _.

Record type_elab {G} A (Ge : context_elab G) := {
  ty : A.type ;
  eqty : forget_type ty = A ;
  isty : Att.istype (ctx Ge) ty
}.

Arguments ty {_ _ _} _.
Arguments eqty {_ _ _} _.
Arguments isty {_ _ _} _.

Record term_elab {G A} u {Ge : context_elab G} (Ae : type_elab A Ge) := {
  tm : A.term ;
  eqtm : forget_term tm = u ;
  istm : Att.isterm (ctx Ge) tm (ty Ae)
}.

Arguments tm {_ _ _ _ _} _.
Arguments eqtm {_ _ _ _ _} _.
Arguments istm {_ _ _ _ _} _.

Record subst_elab {G D} σ (Ge : context_elab G) (De : context_elab D) := {
  sb : A.substitution ;
  eqsb : forget_subst sb = σ ;
  issb : Att.issubst sb (ctx Ge) (ctx De)
}.

Arguments sb {_ _ _ _ _} _.
Arguments eqsb {_ _ _ _ _} _.
Arguments issb {_ _ _ _ _} _.

Axiom admit : forall {A}, A.
Tactic Notation "admit" := (exact admit).

Fixpoint elab_ctx G (H : Ctt.isctx G) {struct H} :
  context_elab G

with elab_type G A (H : Ctt.istype G A) (Ge : context_elab G) {struct H} :
  type_elab A Ge

with elab_term G A u (H : Ctt.isterm G u A)
               (Ge : context_elab G) (Ae : type_elab A Ge) {struct H} :
  term_elab u Ae

with elab_subst G D σ (H : Ctt.issubst σ G D)
                (Ge : context_elab G) (De : context_elab D) {struct H} :
  subst_elab σ Ge De

with elab_eqctx G D (H : Ctt.eqctx G D)
                (Ge : context_elab G) (De : context_elab D) {struct H} :
  Att.eqctx (ctx Ge) (ctx De)
.

Proof.

  (* elab_ctx *)
  - { destruct H ; doConfig.

      (* CtxEmpty *)
      - { exists A.ctxempty.
          - reflexivity.
          - constructor.
        }

      (* CtxExtend *)
      - { pose (Ge := elab_ctx _ i). destruct (elab_ctx _ i) as [G' eG iG].
          pose (Ae := elab_type _ _ i0 Ge).
          destruct (elab_type _ _ i0 Ge) as [A' eA iA].
          (* A tactic to automatically do the above? *)
          exists (A.ctxextend G' A').
          - simpl. rewrite eG. rewrite eA. reflexivity.
          - now capply @CtxExtend.
        }

    }

  (* elab_type *)
  - { destruct H ; doConfig.

      (* TyCtxConv *)
      - { rename Ge into De'.
          pose (De := De').
          destruct De' as [D' eD iD].
          pose (Ge := elab_ctx _ i).
          destruct (elab_ctx _ i) as [G' eG iG].
          pose (Ae := elab_type _ _ H Ge).
          destruct (elab_type _ _ H Ge) as [A' eA iA].
          pose proof (elab_eqctx _ _ e Ge De) as eq.
          exists A'.
          - assumption.
          - simpl. ceapply TyCtxConv.
            + exact iA.
            + simpl. exact eq.
        }

      (* TySubst *)
      - { rename Ge into Ge'. pose (Ge := Ge').
          destruct Ge' as [G' eG iG]. fold Ge.
          pose (De' := elab_ctx _ i1). pose (De := De').
          destruct De' as [D' eD iD].
          pose (Ae' := elab_type _ _ H De). pose (Ae := Ae').
          destruct Ae' as [A' eA iA].
          pose (σe' := elab_subst _ _ _ i Ge De). pose (σe := σe').
          destruct σe' as [σ' eσ iσ].
          exists (A.Subst A' σ').
          - simpl. rewrite eA. rewrite eσ. reflexivity.
          - ceapply @TySubst.
            + exact iσ.
            + assumption.
        }

      (* TyProd *)
      - { rename Ge into Ge'. pose (Ge := Ge').
          destruct Ge' as [G' eG iG]. fold Ge.
          pose (Ae' := elab_type _ _ i Ge). pose (Ae := Ae').
          destruct Ae' as [A' eA iA].
          assert (eGA : forget_ctx (A.ctxextend G' A') = C.ctxextend G A).
          { simpl. rewrite eG. rewrite eA. reflexivity. }
          assert (iGA : Att.isctx (A.ctxextend G' A')).
          { capply @CtxExtend. assumption. }
          pose (GAe :=
                  {| ctx := A.ctxextend G' A' ; eqctx := eGA ; isctx := iGA |}).
          (* Maybe a preliminary lemma to do the above. *)
          pose (Be' := elab_type _ _ H GAe). pose (Be := Be').
          destruct Be' as [B' eB iB].
          exists (A.Prod A' B').
          - simpl. rewrite eA. rewrite eB. reflexivity.
          - simpl. capply @TyProd. assumption.
        }

      (* TyId *)
      - { rename Ge into Ge'. pose (Ge := Ge').
          destruct Ge' as [G' eG iG]. fold Ge.
          pose (Ae' := elab_type _ _ i0 Ge). pose (Ae := Ae').
          destruct Ae' as [A' eA iA].
          pose (ue' := elab_term _ _ _ i1 _ Ae). pose (ue := ue').
          destruct ue' as [u' eu iu].
          pose (ve' := elab_term _ _ _ i2 _ Ae). pose (ve := ve').
          destruct ve' as [v' ev iv].
          exists (A.Id A' u' v').
          - simpl. rewrite eA, eu, ev. reflexivity.
          - now capply @TyId.
        }

      (* TyEmpty *)
      - { rename Ge into Ge'. pose (Ge := Ge').
          destruct Ge' as [G' eG iG]. fold Ge.
          exists A.Empty.
          - simpl. reflexivity.
          - now capply @TyEmpty.
        }

      (* TyUnit *)
      - { rename Ge into Ge'. pose (Ge := Ge').
          destruct Ge' as [G' eG iG]. fold Ge.
          exists A.Unit.
          - simpl. reflexivity.
          - now capply @TyUnit.
        }

      (* TyBool *)
      - { rename Ge into Ge'. pose (Ge := Ge').
          destruct Ge' as [G' eG iG]. fold Ge.
          exists A.Bool.
          - simpl. reflexivity.
          - now capply @TyBool.
        }

      (* TyBinaryProd *)
      - { rename Ge into Ge'. pose (Ge := Ge').
          destruct Ge' as [G' eG iG]. fold Ge.
          pose (Ae' := elab_type _ _ H Ge). pose (Ae := Ae').
          destruct Ae' as [A' eA iA].
          pose (Be' := elab_type _ _ H0 Ge). pose (Be := Be').
          destruct Be' as [B' eB iB].
          exists (A.BinaryProd A' B').
          - simpl. now rewrite eA, eB.
          - now capply @TyBinaryProd.
        }

      (* TyUni *)
      - { rename Ge into Ge'. pose (Ge := Ge').
          destruct Ge' as [G' eG iG]. fold Ge.
          exists (A.Uni n).
          - now simpl.
          - now capply @TyUni.
        }

      (* TyEl *)
      - { rename Ge into Ge'. pose (Ge := Ge').
          destruct Ge' as [G' eG iG]. fold Ge.
          assert (eUni : forget_type (A.Uni l) = C.Uni l) by reflexivity.
          assert (iUni : Att.istype (ctx Ge) (A.Uni l)) by now capply @TyUni.
          pose (Ue := {| ty := A.Uni l ; eqty := eUni ; isty := iUni |}).
          pose (ae' := elab_term _ _ _ i _ Ue). pose (ae := ae').
          destruct ae' as [a' ea ia].
          exists (A.El l a').
          - now simpl.
          - now capply @TyEl.
        }

    }

  (* elab_term *)
  - admit.

  (* elab_subst *)
  - admit.

  (* elab_eqctx *)
  - { destruct H ; doConfig.

      (* CtxRefl *)
      - { destruct Ge as [G' eG iG].
          destruct De as [D' eD iD].
          simpl.
          (* Should we have some result when two expressions erase to the same
             thing? *)
          admit.
        }

      (* CtxSym *)
      - { capply CtxSym. now apply elab_eqctx. }

      (* CtxTrans *)
      - { rename De into Ee.
          pose (De := elab_ctx _ i0).
          config apply @CtxTrans with (D := ctx De).
          - now apply elab_eqctx.
          - now apply elab_eqctx.
        }

      (* EqCtxEmpty *)
      - { destruct Ge as [G' eG iG].
          destruct De as [D' eD iD].
          simpl.
          (* We also should be able to conclude that erasing to the empty
             context implies being the empty context. *)
          admit.
        }

      (* EqCtxExtend *)
      - { destruct Ge as [GA' eGA iGA].
          destruct De as [DB' eDB iDB].
          simpl.
          (* Something similar here. *)
          admit.
        }

    }

Defined.

Close Scope type_scope.

End Translation.
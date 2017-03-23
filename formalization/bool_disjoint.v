Goal true = false -> False.
  exact
    (fun H : true = false =>
       eq_ind true
              (fun e : bool => if e then True else False)
              I
              false
              H
       : False).
Qed.

Goal true = false -> False.
  refine
    (fun H =>
       (eq_ind true (fun e : bool => if e then True -> True else True -> False)
               (fun x => x)
               false
               H : True -> False) I).
Qed.

(* Our proof will be different: We don't have large elimination for equality,
   but we also don't need it because of how TermJ works *)


Section BoolDisjoint.

Require config.
Require Import syntax tt.
Context `{configReflection : config.Reflection}.
Context `{configSimpleProducts : config.SimpleProducts}.
Context `{configProdEta : config.ProdEta}.
Local Instance hasPrecond : config.Precond := {| config.precondFlag := config.No |}.
Local Instance hasCondTy : config.CondTy := {| config.condTyFlag := config.Yes |}.


Let H_eq : type := Id Bool true false.
Let G : context := ctxextend ctxempty H_eq.

Require Import config_tactics.
Require Import checking_tactics.

Let istype_H_eq : istype ctxempty H_eq.
  unfold H_eq. magic.
Defined.

Let isctx_G : isctx G.
  unfold G. magic.
Defined.

Let isterm_true : isterm G true Bool.
magic.
Defined.

Let C : type := CondTy true Unit Empty.
Let A := Bool.
Let u := true.
Let G_A_Equ0 : context :=
  ctxextend
    (ctxextend G A)
    (Id
       (Subst A (sbweak A))
       (subst u (sbweak A))
       (var 0)
    ).

Let istype_C : istype G_A_Equ0 C.
unfold C. unfold G_A_Equ0. unfold A in *. magic.
Qed.
Print istype_C.
Print isctx_G.

Let goal : type := (Prod H_eq Empty).
Let v := false.
Let w := unit.
Let pf : term :=
  lam H_eq Empty
      (j A u C w v (var 0)).

Let isterm_G_w_Csubst :
  isterm G w
         (Subst
            (Subst C
                   (sbshift (Id (Subst A (sbweak A)) (subst u (sbweak A)) (var 0))
                            (sbzero A u))) (sbzero (Id A u u) (refl A u))).
  apply @TermTyConv with (A := Unit).
  - unfold w. magic.
  - unfold A, C.
    pose (Id (Subst Bool (sbweak Bool)) (subst u (sbweak Bool)) (var 0)) as ty_sbs.
    pose (eq_refl ty_sbs).
    unfold ty_sbs in e at 1.
    rewrite e.
    (* congruence to make the contty true compute, then the substs on Unit should go away *)

    admit. (* gocompsubst. *)
    (* + unfold A in *. magic. *)
    (* + eapply EqTyTrans. *)
    (*   admit. *)
  - doConfig.
  - doConfig.
  - doConfig.
Admitted.

Fact bool_disjoint : isterm ctxempty pf goal.
  capply TermAbs.
  pose (@TermJ _ _ _ _ _ G A C u v w (var 0) (fun _ => isctx_G)
               (fun _ => TyBool isctx_G) isterm_true istype_C).



End BoolDisjoint.
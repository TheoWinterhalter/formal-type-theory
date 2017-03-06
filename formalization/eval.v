(* Translating CTT to (E)ITT *)
Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.

Require ctt.
Require eitt.

Module C := ctt.
Module I := eitt.

Definition todolater : False.
Admitted.

Definition todo {A} : A :=
  match todolater return A with end.

Fixpoint eval_ctx (G : C.context) : context :=
  match G with
  | C.ctxempty => ctxempty
  | C.ctxextend G A => ctxextend (eval_ctx G) (eval_type A)
  end

with eval_substitution' (sbs : C.substitution') : substitution :=
  match sbs with
  | C.sbzero G A u => sbzero (eval_type A) (eval_term u)
  | C.sbweak G A => sbweak (eval_type A)
  | C.sbshift G A sbs =>
    sbshift (eval_type A) (eval_substitution sbs)
  | C.sbid G => sbid
  | C.sbcomp sbs sbt =>
    sbcomp (eval_substitution sbs) (eval_substitution sbt)
  end

with eval_substitution (sbs : C.substitution) : substitution :=
  match sbs with
  | C.sbcoerce (c1, c2) sbs' => sbcomp (C.ctxco_map c2)
                                        (sbcomp (eval_substitution' sbs')
                                                  (C.ctxco_inv c1))
  end

with eval_type' (A : C.type') : type :=
  match A with
  | C.Prod A B => Prod (eval_type A) (eval_type B)
  | C.Id A u v => Id (eval_type A) (eval_term u) (eval_term v)
  | C.Subst A sbs => Subst (eval_type A) (eval_substitution sbs)
  | C.Empty => Empty
  | C.Unit => Unit
  | C.Bool => Bool
  end

with eval_type (A : C.type) : type :=
  match A with
  | C.Coerce c A' => Subst (eval_type' A') (C.ctxco_inv c)
  end

with eval_term' (t : C.term') : term :=
  match t with
  | C.var k => var k
  | C.lam A B u => lam (eval_type A) (eval_type B) (eval_term u)
  | C.app u A B v =>
    app (eval_term u) (eval_type A) (eval_type B) (eval_term v)
  | C.refl A u => refl (eval_type A) (eval_term u)
  | C.j A u C w v p => j (eval_type A)
                          (eval_term u)
                          (eval_type C)
                          (eval_term w)
                          (eval_term v)
                          (eval_term p)
  | C.subst u sbs => subst (eval_term u) (eval_substitution sbs)
  | C.exfalso A u => exfalso (eval_type A) (eval_term u)
  | C.unit => unit
  | C.true => true
  | C.false => false
  | C.cond A u v w => cond (eval_type A)
                            (eval_term u)
                            (eval_term v)
                            (eval_term w)
  end

with eval_term (t : C.term) : term :=
  match t with
  | C.coerce (cc, tc) t' => app (C.tyco_map tc)
                               todo
                               todo
                               (subst (eval_term' t') (C.ctxco_map cc))
  end.

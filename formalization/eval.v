(* Translating CTT to (E)ITT *)
Require config.
Require Import config_tactics.

Require Import syntax.
Require Import tt.

Require ctt.

Definition todolater : False.
Admitted.

Definition todo {A} : A :=
  match todolater return A with end.

Fixpoint eval_ctx (G : ctt.context) : context :=
  match G with
  | ctt.ctxempty => ctxempty
  | ctt.ctxextend G A => ctxextend (eval_ctx G) (eval_type A)
  end

with eval_substitution' (sbs : ctt.substitution') : substitution :=
  match sbs with
  | ctt.sbzero A u => sbzero (eval_type A) (eval_term u)
  | ctt.sbweak A => sbweak (eval_type A)
  | ctt.sbshift A sbs =>
    sbshift (eval_type A) (eval_substitution sbs)
  | ctt.sbid => sbid
  | ctt.sbcomp sbs sbt =>
    sbcomp (eval_substitution sbs) (eval_substitution sbt)
  end

with eval_substitution (sbs : ctt.substitution) : substitution :=
  match sbs with
  | ctt.sbcoerce c sbs' => ctt.subst_act c (eval_substitution' sbs')
  end

with eval_type' (A : ctt.type') : type :=
  match A with
  | ctt.Prod A B => Prod (eval_type A) (eval_type B)
  | ctt.Id A u v => Id (eval_type A) (eval_term u) (eval_term v)
  | ctt.Subst A sbs => Subst (eval_type A) (eval_substitution sbs)
  | ctt.Empty => Empty
  | ctt.Unit => Unit
  | ctt.Bool => Bool
  end

with eval_type (A : ctt.type) : type :=
  match A with
  | ctt.Coerce c A' => ctt.type_act c (eval_type' A')
  end

with eval_term' (t : ctt.term') : term :=
  match t with
  | ctt.var k => var k
  | ctt.lam A B u => lam (eval_type A) (eval_type B) (eval_term u)
  | ctt.app u A B v =>
    app (eval_term u) (eval_type A) (eval_type B) (eval_term v)
  | ctt.refl A u => refl (eval_type A) (eval_term u)
  | ctt.j A u C w v p => j (eval_type A)
                          (eval_term u)
                          (eval_type C)
                          (eval_term w)
                          (eval_term v)
                          (eval_term p)
  | ctt.subst u sbs => subst (eval_term u) (eval_substitution sbs)
  | ctt.exfalso A u => exfalso (eval_type A) (eval_term u)
  | ctt.unit => unit
  | ctt.true => true
  | ctt.false => false
  | ctt.cond A u v w => cond (eval_type A)
                            (eval_term u)
                            (eval_term v)
                            (eval_term w)
  end

with eval_term (t : ctt.term) : term :=
  match t with
  | ctt.coerce c t' => ctt.term_act c (eval_term' t')
  end.

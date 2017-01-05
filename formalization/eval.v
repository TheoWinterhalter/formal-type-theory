(* Translating CTT to ITT *)
Require ctt.
Require itt.

Module C := ctt.
Module I := itt.

Definition todolater : False.
Admitted.

Definition todo {A} : A :=
  match todolater return A with end.

Fixpoint eval_ctx (G : C.context) : I.context :=
  match G with
  | C.ctxempty => I.ctxempty
  | C.ctxextend G A => I.ctxextend (eval_ctx G) (eval_type A)
  end

with eval_substitution' (sbs : C.substitution') : I.substitution :=
  match sbs with
  | C.sbzero G A u => I.sbzero (eval_ctx G) (eval_type A) (eval_term u)
  | C.sbweak G A => I.sbweak (eval_ctx G) (eval_type A)
  | C.sbshift G A sbs =>
    I.sbshift (eval_ctx G) (eval_type A) (eval_substitution sbs)
  | C.sbid G => I.sbid (eval_ctx G)
  | C.sbcomp sbs sbt =>
    I.sbcomp (eval_substitution sbs) (eval_substitution sbt)
  end

with eval_substitution (sbs : C.substitution) : I.substitution :=
  match sbs with
  | C.sbcoerce (c1, c2) sbs' => I.sbcomp (C.ctxco_map c2)
                                        (I.sbcomp (eval_substitution' sbs')
                                                  (C.ctxco_inv c1))
  end

with eval_type' (A : C.type') : I.type :=
  match A with
  | C.Prod A B => I.Prod (eval_type A) (eval_type B)
  | C.Id A u v => I.Id (eval_type A) (eval_term u) (eval_term v)
  | C.Subst A sbs => I.Subst (eval_type A) (eval_substitution sbs)
  | C.Empty => I.Empty
  | C.Unit => I.Unit
  | C.Bool => I.Bool
  end

with eval_type (A : C.type) : I.type :=
  match A with
  | C.Coerce c A' => I.Subst (eval_type' A') (C.ctxco_map c)
  end

with eval_term' (t : C.term') : I.term :=
  match t with
  | C.var k => I.var k
  | C.lam A B u => I.lam (eval_type A) (eval_type B) (eval_term u)
  | C.app u A B v =>
    I.app (eval_term u) (eval_type A) (eval_type B) (eval_term v)
  | C.refl A u => I.refl (eval_type A) (eval_term u)
  | C.j A u C w v p => I.j (eval_type A)
                          (eval_term u)
                          (eval_type C)
                          (eval_term w)
                          (eval_term v)
                          (eval_term p)
  | C.subst u sbs => I.subst (eval_term u) (eval_substitution sbs)
  | C.exfalso A u => I.exfalso (eval_type A) (eval_term u)
  | C.unit => I.unit
  | C.true => I.true
  | C.false => I.false
  | C.cond A u v w => I.cond (eval_type A)
                            (eval_term u)
                            (eval_term v)
                            (eval_term w)
  end

with eval_term (t : C.term) : I.term :=
  match t with
  | C.coerce (cc, tc) t' => I.app (C.tyco_map tc)
                                 (* Where do we get the type information
                                    from? *)
                                 todo
                                 todo
                                 (I.subst (eval_term' t') (C.ctxco_map cc))
  end.

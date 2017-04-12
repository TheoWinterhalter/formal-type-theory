Require syntax altsyntax.
Require Import List String.

Definition named_ctx := list altsyntax.variable.

Open Scope type_scope.

Inductive Error := error.

(* Lookup operation to convert a string variable into a de Bruijn index *)
Fixpoint lookup_n (Gx : named_ctx) (x : altsyntax.variable) (n : nat) : nat + Error :=
  match Gx with
  | nil => inr error
  | y :: Gx =>
    match string_dec x y with
    | left eq => inl n
    | right neq => lookup_n Gx x (S n)
    end
  end.

Definition lookup Gx x : nat + Error := lookup_n Gx x 0.


(* First we translate altsyntax back to syntax *)
Fixpoint totype (Gx : named_ctx) (A : altsyntax.type) : syntax.type + Error :=
  match A with
  | altsyntax.Prod x A B =>
    match totype Gx A with
    | inl A' =>
      match totype (x :: Gx) B with
      | inl B' => inl (syntax.Prod A' B')
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.Id A u v =>
    match totype Gx A with
    | inl A' =>
      match toterm Gx u with
      | inl u' =>
        match toterm Gx v with
        | inl v' => inl (syntax.Id A' u' v')
        | inr _ => inr error
        end
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  (* | altsyntax.Subst A sbs => *)
  (*   match totype Gx A with *)
  (*   | inl A' => *)
  (*     match tosubst sbs with *)
  (*     | inl sbs' => inl (syntax.Subst A' sbs') *)
  (*     | inr _ => inr error *)
  (*     end *)
  (*   | inr _ => inr error *)
  (*   end *)

  | altsyntax.Empty => inl syntax.Empty

  | altsyntax.Unit => inl syntax.Unit

  | altsyntax.Bool => inl syntax.Bool

  | altsyntax.SimProd A B =>
    match totype Gx A with
    | inl A' =>
      match totype Gx B with
      | inl B' => inl (syntax.SimProd A' B')
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.Uni n => inl (syntax.Uni n)

  | altsyntax.El a =>
    match toterm Gx a with
    | inl a' => inl (syntax.El a')
    | inr _ => inr error
    end

  end

with toterm (Gx : named_ctx) (u : altsyntax.term) : syntax.term + Error :=
  match u with
  | altsyntax.var x =>
    match lookup Gx x with
    | inl n => inl (syntax.var n)
    | inr _ => inr error
    end

  | altsyntax.lam x A B v =>
    match totype Gx A with
    | inl A' =>
      match totype (x :: Gx) B with
      | inl B' =>
        match toterm (x :: Gx) v with
        | inl v' => inl (syntax.lam A' B' v')
        | inr _ => inr error
        end
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.app u x A B v =>
    match toterm Gx u with
    | inl u' =>
      match totype Gx A with
      | inl A' =>
        match totype (x :: Gx) B with
        | inl B' =>
          match toterm Gx v with
          | inl v' => inl (syntax.app u' A' B' v')
          | inr _ => inr error
          end
        | inr _ => inr error
        end
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.refl A u =>
    match totype Gx A with
    | inl A' =>
      match toterm Gx u with
      | inl u' => inl (syntax.refl A' u')
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.j A u y e C w v p =>
    match totype Gx A with
    | inl A' =>
      match toterm Gx u with
      | inl u' =>
        match totype (e :: y :: Gx) C with
        | inl C' =>
          match toterm Gx w with
          | inl w' =>
            match toterm Gx v with
            | inl v' =>
              match toterm Gx p with
              | inl p' => inl (syntax.j A' u' C' w' v' p')
              | inr _ => inr error
              end
            | inr _ => inr error
            end
          | inr _ => inr error
          end
        | inr _ => inr error
        end
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  (* | altsyntax.subst u sbs => *)
  (*   match toterm Gx u with *)
  (*   | inl u' => *)
  (*     match tosubst sbs with *)
  (*     | inl sbs' => inl (syntax.subst u' sbs') *)
  (*     | inr _ => inr error *)
  (*     end *)
  (*   | inr _ => inr error *)
  (*   end *)

  | altsyntax.exfalso A u =>
    match totype Gx A with
    | inl A' =>
      match toterm Gx u with
      | inl u' => inl (syntax.exfalso A' u')
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.unit => inl (syntax.unit)

  | altsyntax.true => inl (syntax.true)

  | altsyntax.false => inl (syntax.false)

  | altsyntax.cond x C u v w =>
    match totype (x :: Gx) C with
    | inl C' =>
      match toterm Gx u with
      | inl u' =>
        match toterm Gx v with
        | inl v' =>
          match toterm Gx w with
          | inl w' => inl (syntax.cond C' u' v' w')
          | inr _ => inr error
          end
        | inr _ => inr error
        end
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.pair A B u v =>
    match totype Gx A with
    | inl A' =>
      match totype Gx B with
      | inl B' =>
        match toterm Gx u with
        | inl u' =>
          match toterm Gx v with
          | inl v' => inl (syntax.pair A' B' u' v')
          | inr _ => inr error
          end
        | inr _ => inr error
        end
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.proj1 A B p =>
    match totype Gx A with
    | inl A' =>
      match totype Gx B with
      | inl B' =>
        match toterm Gx p with
        | inl p' => inl (syntax.proj1 A' B' p')
        | inr _ => inr error
        end
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.proj2 A B p =>
    match totype Gx A with
    | inl A' =>
      match totype Gx B with
      | inl B' =>
        match toterm Gx p with
        | inl p' => inl (syntax.proj2 A' B' p')
        | inr _ => inr error
        end
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.uniProd n x a b =>
    match toterm Gx a with
    | inl a' =>
      match toterm (x :: Gx) b with
      | inl b' => inl (syntax.uniProd n a' b')
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.uniId n a u v =>
    match toterm Gx a with
    | inl a' =>
      match toterm Gx u with
      | inl u' =>
        match toterm Gx v with
        | inl v' => inl (syntax.uniId n a' u' v')
        | inr _ => inr error
        end
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.uniEmpty n => inl (syntax.uniEmpty n)

  | altsyntax.uniUnit n => inl (syntax.uniUnit n)

  | altsyntax.uniBool n => inl (syntax.uniBool n)

  | altsyntax.uniSimProd n a b =>
    match toterm Gx a with
    | inl a' =>
      match toterm Gx b with
      | inl b' => inl (syntax.uniSimProd n a' b')
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  | altsyntax.uniUni n => inl (syntax.uniUni n)

  end.

(* We won't handle explicit substitutions for now *)
(* with tosubst (Gx : named_ctx) (sbs : altsyntax.substitution) *)
(*   : syntax.substitution + Error := *)
(*   match sbs with *)
(*   | altsyntax.sbvar A x u => *)
(*     (* Is it the right named_ctx for A? *) *)
(*     (* Maybe we need a named_ctx for the codomain as well? *) *)
(*     match totype Gx A with *)
(*     | inl A' => *)
(*       (* Same for u *) *)
(*       match toterm Gx u with *)
(*       | inl u' => *)
(*         match lookup Gx x with *)
(*         | inl n => *)
(*           inl ((fix aux n := *)
(*              match n with *)
(*              | 0 => syntax.sbzero A' u' *)
(*              | S n => syntax.sbshift ??? *)
(*           ) n) *)

(*   | altsyntax.sbid => inl (syntax.sbid) *)

(*   | altsyntax.sbcomp sbs sbt => *)
(*     match tosubst sbs with *)
(*     | inl sbs' => *)
(*       match tosubst sbt with *)
(*       | inl sbt' => inl (syntax.sbcomp sbs' sbt') *)
(*       | inr _ => inr error *)
(*       end *)
(*     | inr _ => inr error *)
(*     end *)

(*   end. *)

Fixpoint toctx (G : altsyntax.context) : (syntax.context * named_ctx) + Error :=
  match G with
  | altsyntax.ctxempty => inl (syntax.ctxempty, nil)

  | altsyntax.ctxextend G x A =>
    match toctx G with
    | inl (G', Gx) =>
      match totype Gx A with
      | inl A' => inl (syntax.ctxextend G' A', x :: Gx)
      | inr _ => inr error
      end
    | inr _ => inr error
    end

  end.

(* We might, later, consider also translating the other way around for
   printing purposes. *)
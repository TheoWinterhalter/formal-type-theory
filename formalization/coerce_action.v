Require Import syntax.
Require Import tt.
Require Import config_tactics.
Require eitt.
Require Import coerce.

(* Coercions are interpreted by certain data and actions in eitt.
   We give the data and the actions here. *)

Structure ctxcoe_data := {
  ctxcoe_act : substitution ;
  ctxcoe_inv : substitution ;
  ctxcoe_act_inv : type -> term ;
  ctxcoe_inv_act : type -> term
}.

Structure tycoe_data := {
  tycoe_act : term ;
  tycoe_inv : term
}.

Structure termcoe_data := {
  termcoe_path : term
}.

Fixpoint ctxcoe_get_data (crc : ctxcoe) : ctxcoe_data

with tycoe_get_data (crc : tycoe) : tycoe_data

with termcoe_get_data (crc : termcoe) : termcoe_data.

Proof.
  (* ctxcoe_get_data *)
  - { destruct crc.

      (* ctxcoe_identity *)
      - exact {| ctxcoe_act := sbid ;
                 ctxcoe_inv := sbid ;
                 ctxcoe_act_inv := (fun _ => var 0) ;
                 ctxcoe_inv_act := (fun _ => var 0)
              |}.
      (* ctxcoe_ctxextend *)
      - { destruct (ctxcoe_get_data crc) as [sbs1 sbs2 u1 u2].
          destruct (tycoe_get_data c2) as [t1 t2].
          (* Data for crc:
             G |- A, D |- B
             sbs1 : G -> D
             sbs2 : D -> G
             G, B sbs1 |- t1 : A [w_{B sbs1}]
             D, A sbs2 |- t2 : B [w_{A sbs2}]

             for every G |- C, u1 gives:
               G, C |- ? : C sbs2 sbs1 weak_C

             for every D |- C, u2 gives:
               D, C |- ? : C sbs1 sbs2 weak_C
          *)
          split.

          - (* want G, A -> D, B *)
            pose (s1 := sbzero (Subst B (sbweak (Subst A sbs2))) t2).
            (* s1 : D, A sbs2 ---> D, A sbs2, B [w_{A sbs2}] *)
            pose (s2 := sbweak (Subst A sbs2)).
            (* s2 : D, A sbs2 ---> D *)
            pose (s3 := sbshift B s2).
            (* s3 : D, A sbs2, B [w_{A sbs2}] ---> D, B *)
            pose (s4 := sbcomp s3 s1).
            (* s4 : D, A sbs2 ---> D, B *)
            pose (s5 := sbshift (Subst A sbs2) sbs1).
            (* s5 : G, (A sbs2) sbs1 ---> D, (A sbs2) *)
            pose (s6 := sbcomp s4 s5).
            (* s6 : G, (A sbs2) sbs1 --> D, B *)
            pose (s7 := sbzero (Subst (Subst (Subst A sbs2) sbs1) (sbweak A)) (u1 A)).
            (* G, A |- "u1 A" : A sbs2 sbs1 weak_A *)
            (* s7 : G, A ---> G, A, A sbs2 sbs1 weak_A *)
            (* sbweak A : G, A ---> G *)
            pose (s8 := sbshift (Subst (Subst A sbs2) sbs1) (sbweak A)).
            (* s8 : G, A, (A sbs2 sbs1 weak_A) ---> G, A sbs2 sbs1 *)
            pose (s9 := sbcomp s8 s7).
            (* s9 : G, A ---> G, A sbs2 sbs1 *)
            exact (sbcomp s6 s9).
            (* G, A, ---> D, B *)

          - (* want D, B -> G, A *)
            (* Symmetry with previous case:
               G ~ D B ~ A, sbs2 ~ sbs1, u2 ~ u1, t2 ~ t1
             *)
            pose (s1 := sbzero (Subst A (sbweak (Subst B sbs1))) t1).
            (* s1 : G, B sbs1 ---> G, B sbs1, A [w_{B sbs1}] *)
            pose (s2 := sbweak (Subst B sbs1)).
            (* s2 : G, B sbs1 ---> G *)
            pose (s3 := sbshift A s2).
            (* s3 : G, B sbs1, A [w_{B sbs1}] ---> G, A *)
            pose (s4 := sbcomp s3 s1).
            (* s4 : G, B sbs1 ---> G, A *)
            pose (s5 := sbshift (Subst B sbs1) sbs2).
            (* s5 : D, (B sbs1) sbs2 ---> G, (B sbs1) *)
            pose (s6 := sbcomp s4 s5).
            (* s6 : D, (B sbs1) sbs2 --> G, A *)
            pose (s7 := sbzero (Subst (Subst (Subst B sbs1) sbs2) (sbweak B)) (u2 B)).
            (* D, B |- "u2 B" : B sbs1 sbs2 weak_B *)
            (* s7 : D, B ---> D, B, B sbs1 sbs2 weak_B *)
            (* sbweak B : D, B ---> D *)
            pose (s8 := sbshift (Subst (Subst B sbs1) sbs2) (sbweak B)).
            (* s8 : D, B, (B sbs1 sbs2 weak_B) ---> D, B sbs1 sbs2 *)
            pose (s9 := sbcomp s8 s7).
            (* s9 : D, B ---> D, B sbs1 sbs2 *)
            exact (sbcomp s6 s9).
            (* D, B, ---> G, A *)

          - { intro C. induction C as [? | ? | C tC sbs | | | | ? ].
              (* Prod *)
              - { todo. }
              (* Id *)
              - { todo. }
              (* Subst *)
              - { todo. (* we die *) }
              (* Empty *)
              - { exact (var 0).  }
              (* Unit *)
              - { exact (var 0). }
              (* Bool *)
              - { exact (var 0). }
              (* SimProd *)
              - { todo. }
            }
          - todo.
        }.

    }

  (* tycoe_get_data *)
  - {
      todo.
    }

  (* termcoe_get_data *)
  - {
      todo.
    }
Defined.


(* Action of coercions on expressions *)

Fixpoint act_subst_left (crc : ctxcoe) (sbs : substitution) : substitution :=
  match crc with
  | ctxcoe_identity => sbs
  | ctxcoe_ctxextend c cA =>
    sbcomp sbs todo
  end.

Fixpoint act_subst_right (crc : ctxcoe) (sbs : substitution) : substitution :=
  match crc with
  | ctxcoe_identity => sbs
  | ctxcoe_ctxextend c cA =>
    sbcomp todo sbs
  end.

Definition act_subst (crc1 crc2 : ctxcoe) (sbs : substitution) :=
  act_subst_left crc1 (act_subst_right crc2 sbs).

Fixpoint act_type (crc : ctxcoe) (A : type) :=
  match crc with
  | ctxcoe_identity => A
  | ctxcoe_ctxextend c cT => todo
  end.

Fixpoint act_term_ctx (crc : ctxcoe) (u : term) : term :=
  match crc with
  | ctxcoe_identity => u
  | ctxcoe_ctxextend c cT => todo
  end.

Fixpoint act_term_type (crc : tycoe) (u : term) {struct crc} : term :=
  match crc with
  | tycoe_identity => u
  | tycoe_prod A1 B1 A2 B2 c cA cB =>
    (* The situation:
       G1 ⊢ A1
       G1, A1 ⊢ B1
       G2 ⊢ A2
       G2, A2 ⊢ B2
       cA : G1 ⊢ A1 ⇒ G2 ⊢ A2 (over c)
       cB : G1, A1 ⊢ B1 ⇒ G2, A2 ⊢ B2 (over c,cA)
     *)
    lam
      A2
      B2
      (act_term_type cB
                     (app (subst u (sbweak A2))
                          (Subst A1 (sbweak A2))
                          (Subst B1 (sbweak A2))
                          (* Note: This should be cA-1, or maybe the
                             product coercion should be refering to cA-1
                             directly! *)
                          (act_term_type cA (var 0))))

  | tycoe_id c cA cu cv => todo (* I'm a bit lost *)
  end.

Definition act_term (crc : ctxcoe) (crt : tycoe) (u : term) : term :=
  act_term_type crt (act_term_ctx crc u).

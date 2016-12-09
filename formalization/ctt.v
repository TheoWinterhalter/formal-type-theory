(* The intermediate type theory with coercions
   (CTT for Coercive Type Theory). *)


Parameter typeCoerce : Type.
Parameter termCoerce : Type.
Parameter substCoerce : Type.

Parameter idTy : typeCoerce.
Parameter idTm : termCoerce.
Parameter idSb : substCoerce.

Inductive context : Type :=
| ctxempty : context
| ctxextend : context -> type -> context

with type' :=
     | Prod : type -> type -> type'
     | Id : type -> term -> term -> type'
     | Subst : type -> substitution -> type'
     | Empty : type'
     | Unit : type'
     | Bool : type'

with type : Type :=
     | Coerce : typeCoerce -> type' -> type

with term' : Type :=
     | var : nat -> term'
     | lam : type -> type -> term -> term'
     | app : term -> type -> type -> term -> term'
     | refl : type -> term -> term'
     | j : type -> term -> type -> term -> term -> term -> term'
     | subst : term -> substitution -> term'
     | exfalso : type -> term -> term'
     | unit : term'
     | true : term'
     | false : term'
     | cond : type -> term -> term -> term -> term'

with term : Type :=
     | coerce : termCoerce -> term' -> term

with substitution' : Type :=
     | sbzero : context -> type -> term -> substitution'
     | sbweak : context -> type -> substitution'
     | sbshift : context -> type -> substitution -> substitution'
     | sbid : context -> substitution'
     | sbcomp : substitution -> substitution -> substitution'

with substitution : Type :=
     | sbcoerce : substCoerce -> substitution' -> substitution.

Inductive isctx : context -> Type :=

     | CtxEmpty :
         isctx ctxempty

     | CtxExtend :
         forall {G A},
           isctx G ->
           istype G A ->
           isctx (ctxextend G A)

with issubst' : substitution' -> context -> context -> Type :=

     | SubstZero :
         forall {G u A},
           isterm G u A ->
           issubst' (sbzero G A u) G (ctxextend G A)

     | SubstWeak :
         forall {G A},
           istype G A ->
           issubst' (sbweak G A) (ctxextend G A) G

     | SubstShift :
         forall {G D A sbs},
           issubst sbs G D ->
           istype D A ->
           issubst' (sbshift G A sbs)
                    (ctxextend G (Coerce idTy (Subst A sbs))) (ctxextend D A)

     | SubstId :
         forall {G},
           isctx G ->
           issubst' (sbid G) G G

     | SubstComp :
         forall {G D E sbs sbt},
           issubst sbs G D ->
           issubst sbt D E ->
           issubst' (sbcomp sbs sbt) G E

with issubst : substitution -> context -> context -> Type :=

     (* Here we need something different than idSb! *)
     | SubstCtxConv :
         forall {G1 G2 D1 D2 sbs},
           issubst' sbs G1 D1 ->
           eqctx G1 G2 ->
           eqctx D1 D2 ->
           issubst (sbcoerce idSb sbs) G2 D2

with istype' : context -> type' -> Type :=

     | TySubst :
         forall {G D A sbs},
           issubst sbs G D ->
           istype D A ->
           istype' G (Subst A sbs)

     | TyProd :
         forall {G A B},
           istype G A ->
           istype (ctxextend G A) B ->
           istype' G (Prod A B)

     | TyId :
         forall {G A u v},
           istype G A ->
           isterm G u A ->
           isterm G v A ->
           istype' G (Id A u v)

     | TyEmpty :
         forall {G},
           isctx G ->
           istype' G Empty

     | TyUnit :
         forall {G},
           isctx G ->
           istype' G Unit

     | TyBool :
         forall {G},
           isctx G ->
           istype' G Bool

with istype : context -> type -> Type :=

     (* idTy is the wrong one here. *)
     | TyCtxConv :
         forall {G D A},
           istype' G A ->
           eqctx G D ->
           istype D (Coerce idTy A)

(* It is unclear whether we want type or type' here. *)
with isterm' : context -> term' -> type -> Type :=

     | TermSubst :
         forall {G D A u sbs},
           issubst sbs G D ->
           isterm D u A ->
           isterm' G (subst u sbs) (Coerce idTy (Subst A sbs))

     | TermVarZero :
         forall {G A},
           istype G A ->
           isterm'(ctxextend G A)
                  (var 0)
                  (Coerce idTy ((Subst A (sbcoerce idSb (sbweak G A)))))

     | TermVarSucc :
         forall {G A B k},
           isterm G (coerce idTm (var k)) A ->
           istype G B ->
           isterm' (ctxextend G B)
                   (var (S k))
                   (Coerce idTy (Subst A (sbcoerce idSb (sbweak G B))))

     | TermAbs :
         forall {G A u B},
           istype G A ->
           isterm (ctxextend G A) u B ->
           isterm' G (lam A B u) (Coerce idTy (Prod A B))

     | TermApp :
         forall {G A B u v},
           istype (ctxextend G A) B ->
           isterm G u (Coerce idTy (Prod A B)) ->
           isterm G v A ->
           isterm' G
                   (app u A B v)
                   (Coerce idTy (Subst B (sbcoerce idSb (sbzero G A v))))

     | TermRefl :
         forall {G A u},
           isterm G u A ->
           isterm' G (refl A u) (Coerce idTy (Id A u u))

     | TermJ :
         forall {G A C u v w p},
           istype G A ->
           isterm G u A ->
           istype
             (ctxextend
                (ctxextend G A)
                (Coerce
                   idTy
                   (Id
                      (Coerce idTy (Subst A (sbcoerce idSb (sbweak G A))))
                      (coerce idTm (subst u (sbcoerce idSb (sbweak G A))))
                      (coerce idTm (var 0))
                   )
                )
             )
             C ->
           isterm G
                  w
                  (Coerce
                     idTy
                     (Subst
                        (Coerce
                           idTy
                           (Subst
                              C
                              (sbcoerce
                                 idSb
                                 (sbshift
                                    G
                                    (Coerce
                                       idTy
                                       (Id
                                          (Coerce
                                             idTy
                                             (Subst A
                                                    (sbcoerce idSb (sbweak G A))))
                                          (coerce
                                             idTm
                                             (subst u
                                                    (sbcoerce idSb (sbweak G A))))
                                          (coerce idTm (var 0)))
                                    )
                                    (sbcoerce idSb (sbzero G A u))
                                 )
                           ))
                        )
                        (sbcoerce
                           idSb
                           (sbzero
                              G
                              (Coerce idTy (Id A u u))
                              (coerce idTm (refl A u)))))
                  ) ->
           isterm G v A ->
           isterm G p (Coerce idTy (Id A u v)) ->
           isterm' G
                   (j A u C w v p)
                   (Coerce
                      idTy
                      (Subst
                         (Coerce
                            idTy
                            (Subst
                               C
                               (sbcoerce
                                  idSb
                                  (sbshift
                                     G
                                     (Coerce
                                        idTy
                                        (Id
                                           (Coerce
                                              idTy
                                              (Subst
                                                 A
                                                 (sbcoerce idSb (sbweak G A))))
                                           (coerce
                                              idTm
                                              (subst
                                                 u
                                                 (sbcoerce idSb (sbweak G A))))
                                           (coerce idTm (var 0)))
                                     )
                                     (sbcoerce idSb (sbzero G A v)))
                            ))
                         )
                         (sbcoerce idSb (sbzero G (Coerce idTy (Id A u v)) p)))
                   )

     | TermExfalso :
         forall {G A u},
           istype G A ->
           isterm G u (Coerce idTy Empty) ->
           isterm' G (exfalso A u) A

     | TermUnit :
         forall {G},
           isctx G ->
           isterm' G unit (Coerce idTy Unit)

     | TermTrue :
         forall {G},
           isctx G ->
           isterm' G true (Coerce idTy Bool)

     | TermFalse :
         forall {G},
           isctx G ->
           isterm' G false (Coerce idTy Bool)

     | TermCond :
         forall {G C u v w},
           isterm G u (Coerce idTy Bool) ->
           istype (ctxextend G (Coerce idTy Bool)) C ->
           isterm
             G v
             (Coerce
                idTy
                (Subst
                   C
                   (sbcoerce
                      idSb
                      (sbzero G (Coerce idTy Bool) (coerce idTm true))))) ->
           isterm
             G w
             (Coerce
                idTy
                (Subst
                   C
                   (sbcoerce
                      idSb
                      (sbzero G (Coerce idTy Bool) (coerce idTm false))))) ->
           isterm' G
                  (cond C u v w)
                  (Coerce
                     idTy
                     (Subst C (sbcoerce idSb (sbzero G (Coerce idTy Bool) u))))

with isterm : context -> term -> type -> Type :=

     (* This shouldn't be idTm. *)
     | TermTyConv :
         forall {G A B u},
           isterm' G u A ->
           eqtype G A B ->
           isterm G (coerce idTm u) B

     | TermCtxConv :
         forall {G D A u},
           isterm' G u A ->
           eqctx G D ->
           isterm D (coerce idTm u) A

with eqctx : context -> context -> Type :=

with eqsubst : substitution -> substitution -> context -> context -> Type :=

with eqtype : context -> type -> type -> Type :=

with eqterm : context -> term -> term -> type -> Type :=
.

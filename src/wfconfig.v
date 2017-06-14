Require Import config.
Require Import tt.

Section WellFormedConfiguration.

Context {ConfigPrecond : config.Precond}.
Context {ConfigReflection : config.Reflection}.
Context {ConfigSimpleProducts : config.SimpleProducts}.
Context {ConfigProdEta : config.ProdEta}.
Context {ConfigUniverses : config.Universes}.
Context {ConfigWithProp : config.WithProp}.
Context {ConfigWithJ : config.WithJ}.
Context {ConfigEmpty : config.WithEmpty}.
Context {ConfigUnit : config.WithUnit}.
Context {ConfigBool : config.WithBool}.
Context {ConfigPi : config.WithPi}.
Context {ConfigExplicitSubstitutions : config.ExplicitSubstitutions}.

Context {ConfigSyntax : config.Syntax}.

(* Admissible rules *)

Open Scope rule_scope.

Class AdmissibleRules := {
  TySubst :
    rule
      parameters: {G D A sbs},
      premise: issubst sbs G D
      premise: istype D A
      precond: isctx G
      precond: isctx D
      conclusion:
        istype G (Subst A sbs)
    endrule ;

  TermSubst :
    rule
      parameters: {G D A u sbs},
      premise: issubst sbs G D
      premise: isterm D u A
      precond: isctx G
      precond: istype D A
      precond: isctx D
      conclusion:
        isterm G (subst u sbs) (Subst A sbs)
    endrule ;

  SubstRefl :
    rule
      parameters: {G D sbs},
      precond: isctx G
      precond: isctx D
      premise: issubst sbs G D
      conclusion:
        eqsubst sbs sbs G D
    endrule ;

  SubstSym :
    rule
      parameters: {G D sbs sbt},
      premise: eqsubst sbs sbt G D
      precond: issubst sbs G D
      precond: issubst sbt G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqsubst sbt sbs G D
    endrule ;

  SubstTrans :
    rule
      parameters: {G D sb1 sb2 sb3},
      premise: eqsubst sb1 sb2 G D
      premise: eqsubst sb2 sb3 G D
      precond: issubst sb1 G D
      precond: issubst sb2 G D
      precond: issubst sb3 G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqsubst sb1 sb3 G D
    endrule ;

  CongSubstZero :
    rule
      parameters: {G A1 A2 u1 u2},
      premise: eqtype G A1 A2
      premise: eqterm G u1 u2 A1
      precond: isctx G
      precond: istype G A1
      precond: istype G A2
      precond: isterm G u1 A1
      precond: isterm G u2 A1
      conclusion:
        eqsubst (sbzero A1 u1)
                (sbzero A2 u2)
                G
                (ctxextend G A1)
    endrule ;

  CongSubstWeak :
    rule
      parameters: {G A1 A2},
      premise: eqtype G A1 A2
      precond: isctx G
      precond: istype G A1
      precond: istype G A2
      conclusion:
        eqsubst (sbweak A1)
                (sbweak A2)
                (ctxextend G A1)
                G
    endrule ;

  CongSubstShift :
    rule
      parameters: {G D A1 A2 sbs1 sbs2},
      premise: eqsubst sbs1 sbs2 G D
      premise: eqtype D A1 A2
      precond: isctx G
      precond: isctx D
      precond: istype D A1
      precond: istype D A2
      precond: issubst sbs1 G D
      precond: issubst sbs2 G D
      conclusion:
        eqsubst (sbshift A1 sbs1)
                (sbshift A2 sbs2)
                (ctxextend G (Subst A1 sbs1))
                (ctxextend D A1)
    endrule ;

  CongSubstComp :
    rule
      parameters: {G D E sbs1 sbs2 sbt1 sbt2},
      premise: eqsubst sbs1 sbs2 G D
      premise: eqsubst sbt1 sbt2 D E
      precond: issubst sbs1 G D
      precond: issubst sbs2 G D
      precond: issubst sbt1 D E
      precond: issubst sbt2 D E
      precond: isctx G
      precond: isctx D
      precond: isctx E
      conclusion:
        eqsubst (sbcomp sbt1 sbs1)
                (sbcomp sbt2 sbs2)
                G
                E
    endrule ;

  EqSubstCtxConv :
    rule
      parameters: {G1 G2 D1 D2 sbs sbt},
      premise: eqsubst sbs sbt G1 D1
      premise: eqctx G1 G2
      premise: eqctx D1 D2
      precond: isctx G1
      precond: isctx G2
      precond: isctx D1
      precond: isctx D2
      precond: issubst sbs G1 D1
      precond: issubst sbt G1 D1
      conclusion:
        eqsubst sbs sbt G2 D2
    endrule ;

  CompAssoc :
    rule
      parameters: {G D E F sbs sbt sbr},
      premise: issubst sbs G D
      premise: issubst sbt D E
      premise: issubst sbr E F
      precond: isctx G
      precond: isctx D
      precond: isctx E
      precond: isctx F
      conclusion:
        eqsubst (sbcomp sbr (sbcomp sbt sbs))
                (sbcomp (sbcomp sbr sbt) sbs)
                G
                F
    endrule ;

  WeakNat :
    rule
      parameters: {G D A sbs},
      precond: isctx G
      precond: isctx D
      premise: issubst sbs G D
      premise: istype D A
      conclusion:
        eqsubst (sbcomp (sbweak A)
                        (sbshift A sbs))
                (sbcomp sbs
                        (sbweak (Subst A sbs)))
                (ctxextend G (Subst A sbs))
                D
    endrule ;

  WeakZero :
    rule
      parameters: {G A u},
      precond: isctx G
      precond: istype G A
      premise: isterm G u A
      conclusion:
        eqsubst (sbcomp (sbweak A) (sbzero A u))
                sbid
                G
                G
    endrule ;

  ShiftZero :
    rule
      parameters: {G D A u sbs},
      precond: isctx G
      precond: isctx D
      precond: istype D A
      premise: issubst sbs G D
      premise: isterm D u A
      conclusion:
        eqsubst (sbcomp (sbshift A sbs)
                        (sbzero (Subst A sbs) (subst u sbs)))
                (sbcomp (sbzero A u)
                        sbs)
                G
                (ctxextend D A)
    endrule ;

  CompShift :
    rule
      parameters: {G D E A sbs sbt},
      precond: isctx G
      precond: isctx D
      precond: isctx E
      premise: issubst sbs G D
      premise: issubst sbt D E
      premise: istype E A
      conclusion:
        eqsubst (sbcomp (sbshift A sbt)
                        (sbshift (Subst A sbt) sbs))
                (sbshift A (sbcomp sbt sbs))
                (ctxextend G (Subst A (sbcomp sbt sbs)))
                (ctxextend E A)
    endrule ;

  CompIdRight :
    rule
      parameters: {G D sbs},
      precond: isctx G
      precond: isctx D
      premise: issubst sbs G D
      conclusion:
        eqsubst (sbcomp sbs sbid) sbs G D
    endrule ;

  CompIdLeft :
    rule
      parameters: {G D sbs},
      precond: isctx G
      precond: isctx D
      premise: issubst sbs G D
        conclusion:
          eqsubst (sbcomp sbid sbs) sbs G D
    endrule ;

  EqTySubstComp :
    rule
      parameters: {G D E A sbs sbt},
      premise: istype E A
      premise: issubst sbs G D
      premise: issubst sbt D E
      precond: isctx G
      precond: isctx D
      precond: isctx E
      conclusion:
        eqtype G
               (Subst (Subst A sbt) sbs)
               (Subst A (sbcomp sbt sbs))
    endrule ;

  EqTySubstProd :
    withpi rule
      parameters: {G D A B sbs},
      premise: issubst sbs G D
      precond: istype D A
      premise: istype (ctxextend D A) B
      precond: isctx G
      precond: isctx D
      conclusion:
        eqtype G
               (Subst (Prod A B) sbs)
               (Prod (Subst A sbs) (Subst B (sbshift A sbs)))
    endrule ;

  EqTySubstId :
    rule
      parameters: {G D A u v sbs},
      premise: issubst sbs G D
      precond: istype D A
      premise: isterm D u A
      premise: isterm D v A
      precond: isctx G
      precond: isctx D
      conclusion:
        eqtype G
               (Subst (Id A u v) sbs)
               (Id (Subst A sbs) (subst u sbs) (subst v sbs))
    endrule ;

  EqTySubstEmpty :
    withempty rule
      parameters: {G D sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqtype G
               (Subst Empty sbs)
               Empty
    endrule ;

  EqTySubstUnit :
    withunit rule
      parameters: {G D sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqtype G
               (Subst Unit sbs)
               Unit
    endrule ;

  EqTySubstBool :
    withbool rule
      parameters: {G D sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqtype G
               (Subst Bool sbs)
               Bool
    endrule ;

  CongTySubst :
    rule
      parameters: {G D A B sbs sbt},
      premise: eqsubst sbs sbt G D
      premise: eqtype D A B
      precond: isctx G
      precond: isctx D
      precond: istype D A
      precond: istype D B
      precond: issubst sbs G D
      precond: issubst sbt G D
      conclusion:
        eqtype G (Subst A sbs) (Subst B sbt)
    endrule ;

  EqTySubstSimProd :
    simpleproduct rule
      parameters: {G D A B sbs},
      precond: isctx G
      precond: isctx D
      premise: issubst sbs G D
      premise: istype D A
      premise: istype D B
      conclusion:
        eqtype G
               (Subst (SimProd A B) sbs)
               (SimProd (Subst A sbs) (Subst B sbs))
    endrule ;

  EqTySubstUni :
    universe rule
      parameters: {G D n sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqtype G
               (Subst (Uni n) sbs)
               (Uni n)
    endrule ;

  ElSubst :
    universe rule
      parameters: {G D a n sbs},
      premise: issubst sbs G D
      premise: isterm D a (Uni n)
      precond: isctx G
      precond: isctx D
      conclusion:
        eqtype G
               (El n (subst a sbs))
               (Subst (El n a) sbs)
    endrule ;

  EqIdSubst :
    rule
      parameters: {G A u},
      precond: isctx G
      precond: istype G A
      premise: isterm G u A
      conclusion:
        eqterm G
               (subst u sbid)
               u
               A
    endrule ;

  EqSubstComp :
    rule
      parameters: {G D E A u sbs sbt},
      premise: isterm E u A
      premise: issubst sbs G D
      premise: issubst sbt D E
      precond: isctx G
      precond: isctx D
      precond: isctx E
      precond: istype E A
      conclusion:
        eqterm G
               (subst (subst u sbt) sbs)
               (subst u (sbcomp sbt sbs))
               (Subst A (sbcomp sbt sbs))
    endrule ;

  EqSubstWeak :
    rule
      parameters: {G A B k},
      precond: isctx G
      precond: istype G A
      premise: isterm G (var k) A
      premise: istype G B
      conclusion:
        eqterm (ctxextend G B)
               (subst (var k) (sbweak B))
               (var (S k))
               (Subst A (sbweak B))
    endrule ;

  EqSubstZeroZero :
    rule
      parameters: {G u A},
      precond: isctx G
      precond: istype G A
      premise: isterm G u A
      conclusion:
        eqterm G
               (subst (var 0) (sbzero A u))
               u
               A
    endrule ;

  EqSubstZeroSucc :
    rule
      parameters: {G A B u k},
      precond: isctx G
      precond: istype G A
      precond: istype G B
      premise: isterm G (var k) A
      premise: isterm G u B
      conclusion:
        eqterm G
               (subst (var (S k)) (sbzero B u))
               (var k)
               A
    endrule ;

  EqSubstShiftZero :
    rule
      parameters: {G D A sbs},
      precond: isctx G
      precond: isctx D
      premise: issubst sbs G D
      premise: istype D A
      conclusion:
        eqterm (ctxextend G (Subst A sbs))
               (subst (var 0) (sbshift A sbs))
               (var 0)
               (Subst (Subst A sbs) (sbweak (Subst A sbs)))
    endrule ;

  EqSubstShiftSucc :
    rule
      parameters: { G D A B sbs k },
      precond: isctx G
      precond: isctx D
      precond: istype D B
      premise: issubst sbs G D
      premise: isterm D (var k) B
      premise: istype D A
      conclusion:
        eqterm (ctxextend G (Subst A sbs))
               (subst (var (S k)) (sbshift A sbs))
               (subst (subst (var k) sbs) (sbweak (Subst A sbs)))
               (Subst (Subst B sbs) (sbweak (Subst A sbs)))
    endrule ;

  EqSubstAbs :
    withpi rule
      parameters: {G D A B u sbs},
      precond: isctx G
      precond: isctx D
      precond: istype D A
      precond: istype (ctxextend D A) B
      premise: isterm (ctxextend D A) u B
      premise: issubst sbs G D
      conclusion:
        eqterm G
               (subst (lam A B u) sbs)
               (lam
                  (Subst A sbs)
                  (Subst B (sbshift A sbs))
                  (subst u (sbshift A sbs)))
               (Prod
                  (Subst A sbs)
                  (Subst B (sbshift A sbs)))
    endrule ;

  EqSubstApp :
    withpi rule
      parameters: {G D A B u v sbs},
      precond: isctx G
      precond: isctx D
      precond: istype D A
      precond: istype (ctxextend D A) B
      premise: isterm D u (Prod A B)
      premise: isterm D v A
      premise: issubst sbs G D
      conclusion:
        eqterm G
               (subst (app u A B v) sbs)
               (app
                  (subst u sbs)
                  (Subst A sbs)
                  (Subst B (sbshift A sbs))
                  (subst v sbs))
               (Subst (Subst B (sbzero A v)) sbs)
    endrule ;

  EqSubstRefl :
    rule
      parameters: {G D A u sbs},
      premise: issubst sbs G D
      premise: isterm D u A
      precond: isctx G
      precond: isctx D
      precond: istype D A
      conclusion:
        eqterm G
               (subst (refl A u) sbs)
               (refl (Subst A sbs) (subst u sbs))
               (Id (Subst A sbs) (subst u sbs) (subst u sbs))
    endrule ;

  EqSubstJ :
    withj rule
      parameters: {G D A C u v w p sbs},
      precond: isctx G
      precond: isctx D
      precond: istype D A
      premise: issubst sbs G D
      premise: isterm D u A
      premise:
        istype
          (ctxextend
             (ctxextend D A)
             (Id
                (Subst A (sbweak A))
                (subst u (sbweak A))
                (var 0)
             )
          )
          C
      premise:
        isterm D
               w
               (Subst
                  (Subst
                     C
                     (sbshift
                        (Id
                           (Subst A (sbweak A))
                           (subst u (sbweak A))
                           (var 0)
                        )
                        (sbzero A u)
                     )
                  )
                  (sbzero (Id A u u) (refl A u))
               )
      premise: isterm D v A
      premise: isterm D p (Id A u v)
      conclusion:
        eqterm G
               (subst
                  (j A u C w v p)
                  sbs
               )
               (j (Subst A sbs)
                  (subst u sbs)
                  (Subst C
                         (sbshift
                            (Id
                               (Subst A (sbweak A))
                               (subst u (sbweak A))
                               (var 0)
                            )
                            (sbshift A sbs)
                         )
                  )
                  (subst w sbs)
                  (subst v sbs)
                  (subst p sbs)
               )
               (Subst
                  (Subst
                     (Subst
                        C
                        (sbshift
                           (Id
                              (Subst A (sbweak A))
                              (subst u (sbweak A))
                              (var 0)
                           )
                           (sbzero A v)
                        )
                     )
                     (sbzero (Id A u v) p)
                  )
                  sbs
               )
    endrule ;

  EqSubstExfalso :
    withempty rule
      parameters: {G D A u sbs},
      precond: isctx G
      precond: isctx D
      premise: istype D A
      premise: isterm D u Empty
      premise: issubst sbs G D
      conclusion:
        eqterm G
               (subst (exfalso A u) sbs)
               (exfalso (Subst A sbs) (subst u sbs))
               (Subst A sbs)
    endrule ;

  EqSubstUnit :
    withunit rule
      parameters: {G D sbs},
      precond: isctx G
      precond: isctx D
      premise: issubst sbs G D
      conclusion:
        eqterm G
               (subst unit sbs)
               unit
               Unit
    endrule ;

  EqSubstTrue :
    withbool rule
      parameters: {G D sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst true sbs)
               true
               Bool
    endrule ;

  EqSubstFalse :
    withbool rule
      parameters: {G D sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst false sbs)
               false
               Bool
    endrule ;

  EqSubstCond :
    withbool rule
      parameters: {G D C u v w sbs},
      precond: isctx G
      precond: isctx D
      premise: issubst sbs G D
      premise: isterm D u Bool
      premise: istype (ctxextend D Bool) C (* TODO: could this be a precond? *)
      premise: isterm D v (Subst C (sbzero Bool true))
      premise: isterm D w (Subst C (sbzero Bool false))
      conclusion:
        eqterm G
               (subst (cond C u v w) sbs)
               (cond (Subst C (sbshift Bool sbs))
                     (subst u sbs)
                     (subst v sbs)
                     (subst w sbs))
               (Subst (Subst C (sbzero Bool u)) sbs)
    endrule ;

  CongTermSubst :
    rule
      parameters: {G D A u1 u2 sbs sbt},
      premise: eqsubst sbs sbt G D
      premise: eqterm D u1 u2 A
      precond: isctx G
      precond: isctx D
      precond: istype D A
      precond: isterm D u1 A
      precond: isterm D u2 A
      precond: issubst sbs G D
      precond: issubst sbt G D
      conclusion:
        eqterm G
               (subst u1 sbs)
               (subst u2 sbt)
               (Subst A sbs)
    endrule ;

  EqSubstPair :
    simpleproduct rule
      parameters: {G D A B u v sbs},
      premise: issubst sbs G D
      premise: isterm D u A
      premise: isterm D v B
      precond: isctx G
      precond: isctx D
      precond: istype D A
      precond: istype D B
      conclusion:
        eqterm G
               (subst (pair A B u v) sbs)
               (pair (Subst A sbs) (Subst B sbs) (subst u sbs) (subst v sbs))
               (SimProd (Subst A sbs) (Subst B sbs))
    endrule ;

  EqSubstProjOne :
    simpleproduct rule
      parameters: {G D A B p sbs},
      premise: issubst sbs G D
      premise: isterm D p (SimProd A B)
      precond: isctx G
      precond: isctx D
      precond: istype D A
      precond: istype D B
      conclusion:
        eqterm G
               (subst (proj1 A B p) sbs)
               (proj1 (Subst A sbs) (Subst B sbs) (subst p sbs))
               (Subst A sbs)
    endrule ;

  EqSubstProjTwo :
    simpleproduct rule
      parameters: {G D A B p sbs},
      premise: issubst sbs G D
      premise: isterm D p (SimProd A B)
      precond: isctx G
      precond: isctx D
      precond: istype D A
      precond: istype D B
      conclusion:
        eqterm G
               (subst (proj2 A B p) sbs)
               (proj2 (Subst A sbs) (Subst B sbs) (subst p sbs))
               (Subst B sbs)
    endrule ;

  EqSubstUniProd :
    universe withpi rule
      parameters: {G D a b n m sbs},
      premise: issubst sbs G D
      premise: isterm D a (Uni (uni n))
      premise: isterm (ctxextend D (El (uni n) a)) b (Uni (uni m))
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst (uniProd (uni n) (uni m) a b) sbs)
               (uniProd (uni n)
                        (uni m)
                        (subst a sbs)
                        (subst b (sbshift (El (uni n) a) sbs)))
               (Uni (uni (max n m)))
    endrule ;

  EqSubstUniProdProp :
    universe withprop withpi rule
      parameters: {G D a b l sbs},
      premise: issubst sbs G D
      premise: isterm D a (Uni l)
      premise: isterm (ctxextend D (El l a)) b (Uni prop)
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst (uniProd l prop a b) sbs)
               (uniProd l prop
                        (subst a sbs)
                        (subst b (sbshift (El l a) sbs)))
               (Uni prop)
    endrule ;

  EqSubstUniId :
    universe rule
      parameters: {G D a u v n sbs},
      premise: issubst sbs G D
      premise: isterm D a (Uni n)
      premise: isterm D u (El n a)
      premise: isterm D v (El n a)
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst (uniId n a u v) sbs)
               (uniId n (subst a sbs) (subst u sbs) (subst v sbs))
               (Uni n)
    endrule ;

  EqSubstUniEmpty :
    withempty universe rule
      parameters: {G D n sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst (uniEmpty n) sbs)
               (uniEmpty n)
               (Uni n)
    endrule ;

  EqSubstUniUnit :
    withunit universe rule
      parameters: {G D n sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst (uniUnit n) sbs)
               (uniUnit n)
               (Uni n)
    endrule ;

  EqSubstUniBool :
    withbool universe rule
      parameters: {G D n sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst (uniBool n) sbs)
               (uniBool n)
               (Uni (uni n))
    endrule ;

  EqSubstUniSimProd :
    universe simpleproduct rule
      parameters: {G D a b n m sbs},
      premise: issubst sbs G D
      premise: isterm D a (Uni (uni n))
      premise: isterm D b (Uni (uni m))
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst (uniSimProd (uni n) (uni m) a b) sbs)
               (uniSimProd (uni n) (uni m) (subst a sbs) (subst b sbs))
               (Uni (uni (max n m)))
    endrule ;

  EqSubstUniSimProdProp :
    universe withprop simpleproduct rule
      parameters: {G D a b sbs},
      premise: issubst sbs G D
      premise: isterm D a (Uni prop)
      premise: isterm D b (Uni prop)
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst (uniSimProd prop prop a b) sbs)
               (uniSimProd prop prop (subst a sbs) (subst b sbs))
               (Uni prop)
    endrule ;

  EqSubstUniUni :
    universe rule
      parameters: {G D n sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst (uniUni (uni n)) sbs)
               (uniUni (uni n))
               (Uni (uni (S n)))
    endrule ;

  EqSubstUniProp :
    universe withprop rule
      parameters: {G D sbs},
      premise: issubst sbs G D
      precond: isctx G
      precond: isctx D
      conclusion:
        eqterm G
               (subst (uniUni prop) sbs)
               (uniUni prop)
               (Uni (uni 0))
    endrule
}.

(* Inversion principles *)

Class CtxExtendInversionClass := {
  CtxExtendInversion : forall G A,
                         isctx (ctxextend G A) ->
                         isctx G * istype G A
}.

Class TyIdInversionClass := {
  TyIdInversion : forall G A u v,
                    istype G (Id A u v) ->
                    isctx G * istype G A * isterm G u A * isterm G v A
}.

Class TyProdInversionClass := {
  TyProdInversion : forall `{_ : Flag withpiFlag} G A B,
                      istype G (Prod A B) ->
                      isctx G * istype G A * istype (ctxextend G A) B
}.

Class TySimProdInversionClass := {
  TySimProdInversion : forall `{_ : Flag simpleproductsFlag} G A B,
                         istype G (SimProd A B) ->
                         isctx G * istype G A * istype G B
}.

Class EqCtxExtendInversionClass := {
  EqCtxExtendInversion : forall G A G' A',
                           eqctx (ctxextend G A) (ctxextend G' A') ->
                           eqctx G G' * eqtype G A A'
}.

End WellFormedConfiguration.

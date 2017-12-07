(* Confgurable type theory. *)

(* Requirements:

   1. Use only letters (no numerals) in rule names, because we define LaTeX macros
      out of them, and those cannot contain numerals.

   2. Do not nest comments inside comments, or else the Python script will break.

*)

Require Import syntax.
Require Import config.

Section TypeTheoryRules.
(* Notations for writing down inference rules. *)

Context `{configPrecondition : config.Precondition}.
Context `{configReflection : config.Reflection}.
Context `{configBinaryProdType : config.BinaryProdType}.
Context `{configProdEta : config.ProdEta}.
Context `{configUniverses : config.Universes}.
Context `{configPropType : config.PropType}.
Context `{configIdEliminator : config.IdEliminator}.
Context `{configEmptyType : config.EmptyType}.
Context `{configUnitType : config.UnitType}.
Context `{configBoolType : config.BoolType}.
Context `{configIdType : config.IdType}.
Context `{configProdType : config.ProdType}.
Context `{configSumType : config.SumType}.
Context `{configSyntax : Syntax}.


Notation "'rule' r 'endrule'" := (r) (at level 96, only parsing).

Notation "'whenReflection' r" :=
  (forall { _ : flagReflection }, r) (only parsing, at level 97).

Notation "'whenBinaryProdType' r" :=
  (forall { _ : flagBinaryProdType }, r) (only parsing, at level 97).

Notation "'whenProdEta' r" :=
  (forall { _ : flagProdEta }, r) (only parsing, at level 97).

Notation "'whenUniverses' r" :=
  (forall { _ : flagUniverses }, r) (only parsing, at level 97).

Notation "'whenPropType' r" :=
  (forall { _ : flagPropType }, r) (only parsing, at level 97).

Notation "'whenIdType' r" :=
  (forall { _ : flagIdType }, r) (only parsing, at level 97).

Notation "'whenIdEliminator' r" :=
  (forall { _ : flagIdEliminator }, r) (only parsing, at level 97).

Notation "'whenEmptyType' r" :=
  (forall { _ : flagEmptyType }, r) (only parsing, at level 97).

Notation "'whenUnitType' r" :=
  (forall { _ : flagUnitType }, r) (only parsing, at level 97).

Notation "'whenBoolType' r" :=
  (forall { _ : flagBoolType }, r) (only parsing, at level 97).

Notation "'whenProdType' r" :=
  (forall { _ : flagProdType }, r) (only parsing, at level 97).

Notation "'whenSumType' r" :=
  (forall { _ : flagSumType }, r) (only parsing, at level 97).

Notation "'parameters:'  x .. y , p" :=
  ((forall x , .. (forall y , p) ..))
    (at level 200, x binder, y binder, right associativity, only parsing).
Notation "'premise:' p q" := (p -> q) (only parsing, at level 95).
Notation "'precond:' p q" := ((flagPrecondition -> p) -> q) (only parsing, at level 95).
Notation "'conclusion:' q" := q (no associativity, only parsing, at level 94).

Inductive isctx : context -> Type :=

     | CtxEmpty :
       rule
         conclusion: isctx ctxempty
       endrule

     | CtxExtend :
       rule
         parameters: {G A},
         precond: isctx G
         premise: istype G A
         conclusion: isctx (ctxextend G A)
       endrule


with issubst : substitution -> context -> context -> Type :=

     | SubstZero :
       rule
         parameters: {G u A},
         premise: isterm G u A
         precond: istype G A
         precond: isctx G
         conclusion:
           issubst (sbzero A u) G (ctxextend G A)
       endrule

     | SubstWeak :
       rule
         parameters: {G A},
         premise: istype G A
         precond: isctx G
         conclusion:
           issubst (sbweak A) (ctxextend G A) G
       endrule

     | SubstShift :
       rule
         parameters: {G D A sbs},
         premise: issubst sbs G D
         premise: istype D A
         precond: isctx G
         precond: isctx D
         conclusion:
           issubst (sbshift A sbs)
                   (ctxextend G (Subst A sbs))
                   (ctxextend D A)
       endrule

     | SubstId :
       rule
         parameters: {G},
         premise: isctx G
         conclusion: issubst sbid G G
       endrule

     | SubstComp :
       rule
         parameters: {G D E sbs sbt},
         premise: issubst sbs G D
         premise: issubst sbt D E
         precond: isctx G
         precond: isctx D
         precond: isctx E
         conclusion:
           issubst (sbcomp sbt sbs) G E
       endrule

     | SubstCtxConv :
       rule
         parameters: {G1 G2 D1 D2 sbs},
         premise: issubst sbs G1 D1
         premise: eqctx G1 G2
         premise: eqctx D1 D2
         precond: isctx G1
         precond: isctx G2
         precond: isctx D1
         precond: isctx D2
         conclusion:
           issubst sbs G2 D2
       endrule


with istype : context -> type -> Type :=

     | TyCtxConv :
       rule
         parameters: {G D A},
         premise: istype G A
         premise: eqctx G D
         precond: isctx G
         precond: isctx D
         conclusion:
           istype D A
       endrule

     | TySubst :
       rule
         parameters: {G D A sbs},
         premise: issubst sbs G D
         premise: istype D A
         precond: isctx G
         precond: isctx D
         conclusion:
           istype G (Subst A sbs)
       endrule

     | TyProd :
       whenProdType rule
         parameters: {G A B},
         premise: istype (ctxextend G A) B
         precond: istype G A
         precond: isctx G
         conclusion:
           istype G (Prod A B)
       endrule

     | TyId :
       whenIdType rule
         parameters: {G A u v},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         premise: isterm G v A
         conclusion:
           istype G (Id A u v)
       endrule

     | TyEmpty :
       whenEmptyType rule
         parameters: {G},
         premise: isctx G
         conclusion:
           istype G Empty
       endrule

     | TyUnit :
       whenUnitType rule
         parameters: {G},
         premise: isctx G
         conclusion:
           istype G Unit
       endrule

     | TyBool :
       whenBoolType rule
         parameters: {G},
         premise: isctx G
         conclusion:
           istype G Bool
       endrule

     | TyBinaryProd :
       whenBinaryProdType rule
         parameters: {G A B},
         precond: isctx G
         premise: istype G A
         premise: istype G B
         conclusion:
           istype G (BinaryProd A B)
       endrule

     | TySum :
       whenSumType rule
         parameters: {G A B},
         premise: istype (ctxextend G A) B
         precond: istype G A
         precond: isctx G
         conclusion:
           istype G (Sum A B)
       endrule

     | TyUni :
       whenUniverses rule
         parameters: {G n},
         premise: isctx G
         conclusion:
           istype G (Uni n)
       endrule

     | TyEl :
       whenUniverses rule
         parameters: {G a l},
         premise: isterm G a (Uni l)
         precond: isctx G
         conclusion:
           istype G (El l a)
       endrule



with isterm : context -> term -> type -> Type :=

     | TermTyConv :
       rule
         parameters: {G A B u},
         premise: isterm G u A
         premise: eqtype G A B
         precond: isctx G
         precond: istype G A
         precond: istype G B
         conclusion:
           isterm G u B
       endrule

     | TermCtxConv :
       rule
         parameters: {G D A u},
         premise: isterm G u A
         premise: eqctx G D
         precond: isctx G
         precond: isctx D
         precond: istype G A
         conclusion:
           isterm D u A
       endrule

     | TermSubst :
       rule
         parameters: {G D A u sbs},
         premise: issubst sbs G D
         premise: isterm D u A
         precond: isctx G
         precond: istype D A
         precond: isctx D
         conclusion:
           isterm G (subst u sbs) (Subst A sbs)
       endrule

     | TermVarZero :
       rule
         parameters: {G A},
         precond: isctx G
         premise: istype G A
         conclusion:
           isterm (ctxextend G A) (var 0) (Subst A (sbweak A))
       endrule

     | TermVarSucc :
       rule
         parameters: {G A B k},
         precond: isctx G
         precond: istype G A
         premise: isterm G (var k) A
         premise: istype G B
         conclusion:
           isterm (ctxextend G B) (var (S k)) (Subst A (sbweak B))
       endrule

     | TermAbs :
       whenProdType rule
         parameters: {G A u B},
         precond: isctx G
         precond: istype G A
         precond: istype (ctxextend G A) B
         premise: isterm (ctxextend G A) u B
         conclusion:
           isterm G (lam A B u) (Prod A B)
       endrule

     | TermApp :
       whenProdType rule
         parameters: {G A B u v},
         precond: isctx G
         precond: istype G A
         precond: istype (ctxextend G A) B
         premise: isterm G u (Prod A B)
         premise: isterm G v A
         conclusion:
           isterm G (app u A B v) (Subst B (sbzero A v))
       endrule

     | TermRefl :
       whenIdType rule
         parameters: {G A u},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         conclusion:
           isterm G (refl A u) (Id A u u)
       endrule

     | TermJ :
       whenIdType whenIdEliminator rule
         parameters: {G A C u v w p},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         premise: istype
             (ctxextend
                (ctxextend G A)
                (Id
                   (Subst A (sbweak A))
                   (subst u (sbweak A))
                   (var 0)
                )
             )
             C
         premise:
           isterm G
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
         premise: isterm G v A
         premise: isterm G p (Id A u v)
         conclusion:
           isterm G
                  (j A u C w v p)
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
       endrule

     | TermExfalso :
       whenEmptyType rule
         parameters: {G A u},
         precond: isctx G
         premise: istype G A
         premise: isterm G u Empty
         conclusion:
           isterm G (exfalso A u) A
       endrule

     | TermUnit :
       whenUnitType rule
         parameters: {G},
         premise: isctx G
         conclusion:
           isterm G unit Unit
       endrule

     | TermTrue :
       whenBoolType rule
         parameters: {G},
         premise: isctx G
         conclusion:
           isterm G true Bool
       endrule

     | TermFalse :
       whenBoolType rule
         parameters: {G},
         premise: isctx G
         conclusion:
           isterm G false Bool
       endrule

     | TermCond :
       whenBoolType rule
         parameters: {G C u v w},
         precond: isctx G
         premise: isterm G u Bool
         premise: istype (ctxextend G Bool) C
         premise: isterm G v (Subst C (sbzero Bool true))
         premise: isterm G w (Subst C (sbzero Bool false))
         conclusion:
           isterm G
                  (cond C u v w)
                  (Subst C (sbzero Bool u))
       endrule

     | TermPair :
       whenBinaryProdType rule
         parameters: {G A B u v},
         precond: isctx G
         precond: istype G A
         precond: istype G B
         premise: isterm G u A
         premise: isterm G v B
         conclusion:
           isterm G (pair A B u v) (BinaryProd A B)
       endrule

     | TermProjOne :
       whenBinaryProdType rule
         parameters: {G A B p},
         precond: isctx G
         precond: istype G A
         precond: istype G B
         premise: isterm G p (BinaryProd A B)
         conclusion:
           isterm G (proj1 A B p) A
       endrule

     | TermProjTwo :
       whenBinaryProdType rule
         parameters: {G A B p},
         precond: isctx G
         precond: istype G A
         precond: istype G B
         premise: isterm G p (BinaryProd A B)
         conclusion:
           isterm G (proj2 A B p) B
       endrule

     | TermEx :
       whenSumType rule
         parameters: {G A B a b},
         premise: isterm G a A
         premise: isterm G b (Subst B (sbzero A a))
         precond: istype G A
         precond: istype (ctxextend G A) B
         precond: isctx G
         conclusion:
           isterm G (ex A B a b) (Sum A B)
       endrule

     | TermSumElim :
       whenSumType rule
         parameters: {G A B C p c},
         premise: isterm G p (Sum A B)
         premise: istype (ctxextend G (Sum A B)) C
         premise:
           isterm (ctxextend (ctxextend G A) B)
                  c
                  (Subst C (sbzero (Sum A B) (ex A B (var 1) (var 0))))
         precond: istype G A
         precond: istype (ctxextend G A) B
         precond: isctx G
         conclusion:
           isterm G (sumelim A B C p c) (Subst C (sbzero (Sum A B) p))
       endrule

     | TermUniProd :
       whenUniverses whenProdType rule
         parameters: {G a b n m},
         premise: isterm G a (Uni (uni n))
         premise: isterm (ctxextend G (El (uni n) a)) b (Uni (uni m))
         precond: isctx G
         conclusion:
           isterm G (uniProd (uni n) (uni m) a b) (Uni (uni (max n m)))
       endrule

     | TermUniProdProp :
       whenUniverses whenPropType whenProdType rule
         parameters: {G a b l},
         premise: isterm G a (Uni l)
         premise: isterm (ctxextend G (El l a)) b (Uni prop)
         precond: isctx G
         conclusion:
           isterm G (uniProd l prop a b) (Uni prop)
       endrule

     | TermUniId :
       whenUniverses whenIdType rule
         parameters: {G a u v n},
         premise: isterm G a (Uni n)
         premise: isterm G u (El n a)
         premise: isterm G v (El n a)
         precond: isctx G
         conclusion:
           isterm G (uniId n a u v) (Uni n)
       endrule

     | TermUniEmpty :
       whenEmptyType whenUniverses rule
         parameters: {G n},
         premise: isctx G
         conclusion:
           isterm G (uniEmpty n) (Uni n)
       endrule

     | TermUniUnit :
       whenUnitType whenUniverses rule
         parameters: {G n},
         premise: isctx G
         conclusion:
           isterm G (uniUnit n) (Uni n)
       endrule

     | TermUniBool :
       whenBoolType whenUniverses rule
         parameters: {G n},
         premise: isctx G
         conclusion:
           isterm G (uniBool n) (Uni (uni n))
       endrule

     | TermUniBinaryProd :
       whenUniverses whenBinaryProdType rule
         parameters: {G a b n m},
         premise: isterm G a (Uni (uni n))
         premise: isterm G b (Uni (uni m))
         precond: isctx G
         conclusion:
           isterm G (uniBinaryProd (uni n) (uni m) a b) (Uni (uni (max n m)))
       endrule

     | TermUniSum :
       whenUniverses whenSumType rule
         parameters: {G a b n m},
         premise: isterm G a (Uni (uni n))
         premise: isterm (ctxextend G (El (uni n) a)) b (Uni (uni m))
         precond: isctx G
         conclusion:
           isterm G (uniSum (uni n) (uni m) a b) (Uni (uni (max n m)))
       endrule

     | TermUniBinaryProdProp :
       whenUniverses whenPropType whenBinaryProdType rule
         parameters: {G a b},
         premise: isterm G a (Uni prop)
         premise: isterm G b (Uni prop)
         precond: isctx G
         conclusion:
           isterm G (uniBinaryProd prop prop a b) (Uni prop)
       endrule

     | TermUniSumProp :
       whenUniverses whenPropType whenSumType rule
         parameters: {G a b},
         premise: isterm G a (Uni prop)
         premise: isterm (ctxextend G (El prop a)) b (Uni prop)
         precond: isctx G
         conclusion:
           isterm G (uniSum prop prop a b) (Uni prop)
       endrule

     | TermUniUni :
       whenUniverses rule
         parameters: {G n},
         premise: isctx G
         conclusion:
           isterm G (uniUni (uni n)) (Uni (uni (S n)))
       endrule

     | TermUniProp :
       whenUniverses whenPropType rule
         parameters: {G},
         premise: isctx G
         conclusion:
           isterm G (uniUni prop) (Uni (uni 0))
       endrule


with eqctx : context -> context -> Type :=


     | CtxRefl :
       rule
         parameters: {G},
         premise: isctx G
         conclusion:
           eqctx G G
       endrule

     | CtxSym :
       rule
         parameters: {G D},
         premise: eqctx G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqctx D G
       endrule

     | CtxTrans :
       rule
         parameters: {G D E},
         precond: isctx G
         precond: isctx D
         precond: isctx E
         premise: eqctx G D
         premise: eqctx D E
         conclusion:
           eqctx G E
       endrule

     | EqCtxEmpty :
       rule
         conclusion:
           eqctx ctxempty ctxempty
       endrule

     | EqCtxExtend :
       rule
         parameters: {G D A B},
         precond: isctx G
         precond: isctx D
         precond: istype G A
         precond: istype G B
         premise: eqctx G D
         premise: eqtype G A B
         conclusion:
           eqctx (ctxextend G A) (ctxextend D B)
       endrule

with eqsubst : substitution -> substitution -> context -> context -> Type :=

     | SubstRefl :
       rule
         parameters: {G D sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         conclusion:
           eqsubst sbs sbs G D
       endrule

     | SubstSym :
       rule
         parameters: {G D sbs sbt},
         premise: eqsubst sbs sbt G D
         precond: issubst sbs G D
         precond: issubst sbt G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqsubst sbt sbs G D
       endrule

     | SubstTrans :
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
       endrule

     | CongSubstZero :
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
       endrule

     | CongSubstWeak :
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
       endrule

     | CongSubstShift :
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
       endrule

     | CongSubstComp :
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
       endrule

     | EqSubstCtxConv :
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
       endrule

     | CompAssoc :
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
       endrule

     | WeakNat :
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
       endrule

     | WeakZero :
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
       endrule

     | ShiftZero :
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
       endrule

     | CompShift :
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
       endrule

     | CompIdRight :
       rule
         parameters: {G D sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         conclusion:
           eqsubst (sbcomp sbs sbid) sbs G D
       endrule

     | CompIdLeft :
       rule
         parameters: {G D sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         conclusion:
           eqsubst (sbcomp sbid sbs) sbs G D
       endrule


with eqtype : context -> type -> type -> Type :=

     | EqTyCtxConv :
       rule
         parameters: {G D A B},
         premise: eqtype G A B
         premise: eqctx G D
         precond: istype G A
         precond: istype G B
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype D A B
       endrule

     | EqTyRefl:
       rule
         parameters: {G A},
         precond: isctx G
         premise: istype G A
         conclusion:
           eqtype G A A
       endrule

     | EqTySym :
       rule
         parameters: {G A B},
         premise: eqtype G A B
         precond: istype G A
         precond: istype G B
         precond: isctx G
         conclusion:
           eqtype G B A
       endrule

     | EqTyTrans :
       rule
         parameters: {G A B C},
         premise: eqtype G A B
         premise: eqtype G B C
         precond: isctx G
         precond: istype G A
         precond: istype G B
         precond: istype G C
         conclusion:
           eqtype G A C
       endrule

     | EqTyIdSubst :
       rule
         parameters: {G A},
         precond: isctx G
         premise: istype G A
         conclusion:
           eqtype G
                  (Subst A sbid)
                  A
       endrule

     | EqTySubstComp :
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
       endrule


     | EqTySubstProd :
       whenProdType rule
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
       endrule

     | EqTySubstId :
       whenIdType rule
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
       endrule

     | EqTySubstEmpty :
       whenEmptyType rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (Subst Empty sbs)
                  Empty
       endrule

     | EqTySubstUnit :
       whenUnitType rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (Subst Unit sbs)
                  Unit
       endrule

     | EqTySubstBool :
       whenBoolType rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (Subst Bool sbs)
                  Bool
       endrule

     | EqTyExfalso :
       whenEmptyType rule
         parameters: {G A B u},
         precond: isctx G
         premise: istype G A
         premise: istype G B
         premise: isterm G u Empty
         conclusion:
           eqtype G A B
       endrule

     | CongProd :
       whenProdType rule
         parameters: {G A1 A2 B1 B2},
         precond: isctx G
         precond: istype G A1
         precond: istype (ctxextend G A1) A2
         precond: istype G B1
         precond: istype (ctxextend G A1) B2
         premise: eqtype G A1 B1
         premise: eqtype (ctxextend G A1) A2 B2
         conclusion:
           eqtype G (Prod A1 A2) (Prod B1 B2)
       endrule

     | CongId :
       whenIdType rule
         parameters: {G A B u1 u2 v1 v2},
         precond: isctx G
         precond: istype G A
         precond: istype G B
         precond: isterm G u1 A
         precond: isterm G u2 A
         precond: isterm G v1 A
         precond: isterm G v2 A
         premise: eqtype G A B
         premise: eqterm G u1 v1 A
         premise: eqterm G u2 v2 A
         conclusion:
           eqtype G (Id A u1 u2) (Id B v1 v2)
       endrule

     | CongTySubst :
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
       endrule

     | CongBinaryProd :
       whenBinaryProdType rule
         parameters: {G A1 A2 B1 B2},
         precond: isctx G
         precond: istype G A1
         precond: istype G A2
         precond: istype G B1
         precond: istype G B2
         premise: eqtype G A1 A2
         premise: eqtype G B1 B2
         conclusion:
           eqtype G (BinaryProd A1 B1) (BinaryProd A2 B2)
       endrule

     | EqTySubstBinaryProd :
       whenBinaryProdType rule
         parameters: {G D A B sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         premise: istype D A
         premise: istype D B
         conclusion:
           eqtype G
                  (Subst (BinaryProd A B) sbs)
                  (BinaryProd (Subst A sbs) (Subst B sbs))
       endrule

     | CongSum :
       whenSumType rule
         parameters: {G A1 A2 B1 B2},
         precond: isctx G
         precond: istype G A1
         precond: istype (ctxextend G A1) A2
         precond: istype G B1
         precond: istype (ctxextend G A1) B2
         premise: eqtype G A1 B1
         premise: eqtype (ctxextend G A1) A2 B2
         conclusion:
           eqtype G (Sum A1 A2) (Sum B1 B2)
       endrule

     | EqTySubstSum :
       whenSumType rule
         parameters: {G D A B sbs},
         premise: issubst sbs G D
         precond: istype D A
         premise: istype (ctxextend D A) B
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (Subst (Sum A B) sbs)
                  (Sum (Subst A sbs) (Subst B (sbshift A sbs)))
       endrule

     | EqTySubstUni :
       whenUniverses rule
         parameters: {G D n sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (Subst (Uni n) sbs)
                  (Uni n)
       endrule

     | ElProd :
       whenUniverses whenProdType rule
         parameters: {G a b n m},
         premise: isterm G a (Uni (uni n))
         premise: isterm (ctxextend G (El (uni n) a)) b (Uni (uni m))
         precond: isctx G
         conclusion:
           eqtype G
                  (El (uni (max n m)) (uniProd (uni n) (uni m) a b))
                  (Prod (El (uni n) a) (El (uni m) b))
       endrule

     | ElProdProp :
       whenUniverses whenPropType whenProdType rule
         parameters: {G a b l},
         premise: isterm G a (Uni l)
         premise: isterm (ctxextend G (El l a)) b (Uni prop)
         precond: isctx G
         conclusion:
           eqtype G
                  (El prop (uniProd l prop a b))
                  (Prod (El l a) (El prop b))
       endrule

     | ElId :
       whenUniverses whenIdType rule
         parameters: {G a u v n},
         premise: isterm G a (Uni n)
         premise: isterm G u (El n a)
         premise: isterm G v (El n a)
         precond: isctx G
         conclusion:
           eqtype G
                  (El n (uniId n a u v))
                  (Id (El n a) u v)
       endrule

     | ElSubst :
       whenUniverses rule
         parameters: {G D a n sbs},
         premise: issubst sbs G D
         premise: isterm D a (Uni n)
         precond: isctx G
         precond: isctx D
         conclusion:
           eqtype G
                  (El n (subst a sbs))
                  (Subst (El n a) sbs)
       endrule

     | ElEmpty :
       whenEmptyType whenUniverses rule
         parameters: {G n},
         premise: isctx G
         conclusion:
           eqtype G
                  (El n (uniEmpty n))
                  Empty
       endrule

     | ElUnit :
       whenUnitType whenUniverses rule
         parameters: {G n},
         premise: isctx G
         conclusion:
           eqtype G
                  (El n (uniUnit n))
                  Unit
       endrule

     | ElBool :
       whenBoolType whenUniverses rule
         parameters: {G n},
         premise: isctx G
         conclusion:
           eqtype G
                  (El (uni n) (uniBool n))
                  Bool
       endrule

     | ElBinaryProd :
       whenUniverses whenBinaryProdType rule
         parameters: {G a b n m},
         premise: isterm G a (Uni (uni n))
         premise: isterm G b (Uni (uni m))
         precond: isctx G
         conclusion:
           eqtype G
                  (El (uni (max n m)) (uniBinaryProd (uni n) (uni m) a b))
                  (BinaryProd (El (uni n) a) (El (uni m) b))
       endrule

     | ElBinaryProdProp :
       whenUniverses whenPropType whenBinaryProdType rule
         parameters: {G a b},
         premise: isterm G a (Uni prop)
         premise: isterm G b (Uni prop)
         precond: isctx G
         conclusion:
           eqtype G
                  (El prop (uniBinaryProd prop prop a b))
                  (BinaryProd (El prop a) (El prop b))
       endrule

     | ElSum :
       whenUniverses whenSumType rule
         parameters: {G a b n m},
         premise: isterm G a (Uni (uni n))
         premise: isterm (ctxextend G (El (uni n) a)) b (Uni (uni m))
         precond: isctx G
         conclusion:
           eqtype G
                  (El (uni (max n m)) (uniSum (uni n) (uni m) a b))
                  (Sum (El (uni n) a) (El (uni m) b))
       endrule

     | ElSumProp :
       whenUniverses whenPropType whenSumType rule
         parameters: {G a b},
         premise: isterm G a (Uni prop)
         premise: isterm (ctxextend G (El prop a)) b (Uni prop)
         precond: isctx G
         conclusion:
           eqtype G
                  (El prop (uniSum prop prop a b))
                  (Sum (El prop a) (El prop b))
       endrule

     | ElUni :
       whenUniverses rule
         parameters: {G n},
         premise: isctx G
         conclusion:
           eqtype G
                  (El (uni (S n)) (uniUni (uni n)))
                  (Uni (uni n))
       endrule

     | ElProp :
       whenUniverses whenPropType rule
         parameters: {G},
         premise: isctx G
         conclusion:
           eqtype G
                  (El (uni 0) (uniUni prop))
                  (Uni prop)
       endrule

     | CongEl :
       whenUniverses rule
         parameters: {G a b n},
         premise: eqterm G a b (Uni n)
         precond: isterm G a (Uni n)
         precond: isterm G b (Uni n)
         precond: isctx G
         conclusion:
           eqtype G
                  (El n a)
                  (El n b)
       endrule


with eqterm : context -> term -> term -> type -> Type :=

     | EqTyConv :
       rule
         parameters: {G A B u v},
         premise: eqterm G u v A
         premise: eqtype G A B
         precond: isctx G
         precond: istype G A
         precond: istype G B
         precond: isterm G u A
         precond: isterm G v A
         conclusion:
           eqterm G u v B
       endrule

     | EqCtxConv :
       rule
         parameters: {G D u v A},
         precond: isctx G
         precond: isctx D
         precond: istype G A
         precond: isterm G u A
         precond: isterm G v A
         premise: eqterm G u v A
         premise: eqctx G D
         conclusion:
           eqterm D u v A
       endrule

     | EqRefl :
       rule
         parameters: {G A u},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         conclusion:
           eqterm G u u A
       endrule

     | EqSym :
       rule
         parameters: {G A u v},
         premise: eqterm G v u A
         precond: isterm G u A
         precond: isterm G v A
         precond: istype G A
         precond: isctx G
         conclusion:
           eqterm G u v A
       endrule

     | EqTrans :
       rule
         parameters: {G A u v w},
         premise: eqterm G u v A
         premise: eqterm G v w A
         precond: isctx G
         precond: istype G A
         precond: isterm G u A
         precond: isterm G v A
         precond: isterm G w A
         conclusion:
           eqterm G u w A
       endrule


     | EqIdSubst :
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
       endrule

     | EqSubstComp :
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
       endrule

     | EqSubstWeak :
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
       endrule


     | EqSubstZeroZero :
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
       endrule

     | EqSubstZeroSucc :
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
       endrule

     | EqSubstShiftZero :
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
       endrule

     | EqSubstShiftSucc :
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
       endrule

     | EqSubstAbs :
       whenProdType rule
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
       endrule

     | EqSubstApp :
       whenProdType rule
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
       endrule

     | EqSubstRefl :
       whenIdType rule
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
       endrule

     | EqSubstJ :
       whenIdType whenIdEliminator rule
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
       endrule

     (* This rule is subsumed by EqTermExfalso *)
     | EqSubstExfalso :
       whenEmptyType rule
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
       endrule

     | EqSubstUnit :
       whenUnitType rule
         parameters: {G D sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         conclusion:
           eqterm G
                  (subst unit sbs)
                  unit
                  Unit
       endrule

     | EqSubstTrue :
       whenBoolType rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst true sbs)
                  true
                  Bool
       endrule

     | EqSubstFalse :
       whenBoolType rule
         parameters: {G D sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst false sbs)
                  false
                  Bool
       endrule

     | EqSubstCond :
       whenBoolType rule
         parameters: {G D C u v w sbs},
         precond: isctx G
         precond: isctx D
         premise: issubst sbs G D
         premise: isterm D u Bool
         premise: istype (ctxextend D Bool) C (* TODO: could this be a precondition? *)
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
       endrule

     | EqTermExfalso :
       whenEmptyType rule
         parameters: {G A u v w},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         premise: isterm G v A
         premise: isterm G w Empty
         conclusion:
           eqterm G u v A
       endrule

     | UnitEta :
       whenUnitType rule
         parameters: {G u v},
         precond: isctx G
         premise: isterm G u Unit
         premise: isterm G v Unit
         conclusion:
           eqterm G u v Unit
       endrule

     | EqReflection :
       whenReflection whenIdType rule
         parameters: {G A u v p},
         precond: isctx G
         precond: istype G A
         precond: isterm G u A
         precond: isterm G v A
         premise: isterm G p (Id A u v)
         conclusion:
           eqterm G u v A
       endrule

     | ProdBeta :
       whenProdType rule
         parameters: {G A B u v},
         precond: isctx G
         precond: istype G A
         precond: istype (ctxextend G A) B
         premise: isterm (ctxextend G A) u B
         premise: isterm G v A
         conclusion:
           eqterm G
                  (app (lam A B u) A B v)
                  (subst u (sbzero A v))
                  (Subst B (sbzero A v))
       endrule

     | CondTrue :
       whenBoolType rule
         parameters: {G C v w},
         precond: isctx G
         premise: istype (ctxextend G Bool) C
         premise: isterm G v (Subst C (sbzero Bool true))
         premise: isterm G w (Subst C (sbzero Bool false))
         conclusion:
           eqterm G
                  (cond C true v w)
                  v
                  (Subst C (sbzero Bool true))
       endrule

     | CondFalse :
       whenBoolType rule
         parameters: {G C v w},
         precond: isctx G
         premise: istype (ctxextend G Bool) C
         premise: isterm G v (Subst C (sbzero Bool true))
         premise: isterm G w (Subst C (sbzero Bool false))
         conclusion:
           eqterm G
                  (cond C false v w)
                  w
                  (Subst C (sbzero Bool false))
       endrule

     | ProdEta :
       whenProdEta whenProdType rule
         parameters: {G A B u v},
         precond: isctx G
         precond: istype G A
         precond: istype (ctxextend G A) B
         premise: isterm G u (Prod A B)
         premise: isterm G v (Prod A B)
         premise: eqterm (ctxextend G A)
                  (app (subst u (sbweak A))
                       (Subst A (sbweak A))
                       (Subst B (sbshift A (sbweak A)))
                       (var 0))
                  (app (subst v (sbweak A))
                       (Subst A (sbweak A))
                       (Subst B (sbshift A (sbweak A)))
                       (var 0))
                  B
         conclusion:
           eqterm G u v (Prod A B)
       endrule

     | JRefl :
       whenIdType whenIdEliminator rule
         parameters: {G A C u w},
         precond: isctx G
         precond: istype G A
         premise: isterm G u A
         premise: istype
             (ctxextend
                (ctxextend G A)
                (Id
                   (Subst A (sbweak A))
                   (subst u (sbweak A))
                   (var 0)
                )
             )
             C
         premise: isterm G
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
         conclusion:
           eqterm G
                  (j A u C w u (refl A u))
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
       endrule

     | CongAbs :
       whenProdType rule
         parameters: {G A1 A2 B1 B2 u1 u2},
         precond: isctx G
         precond: istype G A1
         precond: istype G B1
         precond: istype (ctxextend G A1) A2
         precond: istype (ctxextend G A1) B2
         precond: isterm (ctxextend G A1) u1 A2
         precond: isterm (ctxextend G A1) u2 A2
         premise: eqtype G A1 B1
         premise: eqtype (ctxextend G A1) A2 B2
         premise: eqterm (ctxextend G A1) u1 u2 A2
         conclusion:
           eqterm G
                  (lam A1 A2 u1)
                  (lam B1 B2 u2)
                  (Prod A1 A2)
       endrule

     | CongApp :
       whenProdType rule
         parameters: {G A1 A2 B1 B2 u1 u2 v1 v2},
         precond: isctx G
         precond: istype G A1
         precond: istype (ctxextend G A1) A2
         precond: istype G B1
         precond: istype (ctxextend G A1) B2
         precond: isterm G u1 (Prod A1 A2)
         precond: isterm G v1 (Prod A1 A2)
         precond: isterm G u2 A1
         precond: isterm G v2 A1
         premise: eqtype G A1 B1
         premise: eqtype (ctxextend G A1) A2 B2
         premise: eqterm G u1 v1 (Prod A1 A2)
         premise: eqterm G u2 v2 A1
         conclusion:
           eqterm G
                  (app u1 A1 A2 u2)
                  (app v1 B1 B2 v2)
                  (Subst A2 (sbzero A1 u2))
       endrule

     | CongRefl :
       whenIdType rule
         parameters: {G u1 u2 A1 A2},
         precond: isctx G
         precond: istype G A1
         precond: istype G A2
         precond: isterm G u1 A1
         precond: isterm G u2 A1
         premise: eqterm G u1 u2 A1
         premise: eqtype G A1 A2
         conclusion:
           eqterm G
                  (refl A1 u1)
                  (refl A2 u2)
                  (Id A1 u1 u1)
       endrule

     | CongJ :
       whenIdType whenIdEliminator rule
         parameters: {G A1 A2 C1 C2 u1 u2 v1 v2 w1 w2 p1 p2},
         precond: isctx G
         precond: istype G A1
         precond: istype G A2
         precond:
           istype
             (ctxextend
                (ctxextend G A1)
                (Id
                   (Subst A1 (sbweak A1))
                   (subst u1 (sbweak A1))
                   (var 0)
                )
             )
             C1
         precond:
           istype
             (ctxextend
                (ctxextend G A1)
                (Id
                   (Subst A1 (sbweak A1))
                   (subst u1 (sbweak A1))
                   (var 0)
                )
             )
             C2
         precond: isterm G u1 A1
         precond: isterm G u2 A1
         precond: isterm G v1 A1
         precond: isterm G v2 A1
         precond: isterm G p1 (Id A1 u1 v1)
         precond: isterm G p2 (Id A1 u1 v1)
         premise: eqtype G A1 A2
         premise: eqterm G u1 u2 A1
         premise:
           eqtype
             (ctxextend
                (ctxextend G A1)
                (Id
                   (Subst A1 (sbweak A1))
                   (subst u1 (sbweak A1))
                   (var 0)
                )
             )
             C1
             C2
         precond:
            isterm G
                  w1
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (Id
                              (Subst A1 (sbweak A1))
                              (subst u1 (sbweak A1))
                              (var 0)
                           )
                           (sbzero A1 u1)
                        )
                     )
                     (sbzero (Id A1 u1 u1) (refl A1 u1))
                  )
         precond:
            isterm G
                  w2
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (Id
                              (Subst A1 (sbweak A1))
                              (subst u1 (sbweak A1))
                              (var 0)
                           )
                           (sbzero A1 u1)
                        )
                     )
                     (sbzero (Id A1 u1 u1) (refl A1 u1))
                  )
         premise:
            eqterm G
                  w1
                  w2
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (Id
                              (Subst A1 (sbweak A1))
                              (subst u1 (sbweak A1))
                              (var 0)
                           )
                           (sbzero A1 u1)
                        )
                     )
                     (sbzero (Id A1 u1 u1) (refl A1 u1))
                  )
         premise: eqterm G v1 v2 A1
         premise: eqterm G p1 p2 (Id A1 u1 v1)
         conclusion:
           eqterm G
                  (j A1 u1 C1 w1 v1 p1)
                  (j A2 u2 C2 w2 v2 p2)
                  (Subst
                     (Subst
                        C1
                        (sbshift
                           (Id
                              (Subst A1 (sbweak A1))
                              (subst u1 (sbweak A1))
                              (var 0)
                           )
                           (sbzero A1 v1)
                        )
                     )
                     (sbzero (Id A1 u1 v1) p1)
                  )
       endrule

     (* This rule doesn't seem necessary as subsumed by EqTermexfalso! *)
     (* | CongExfalso : *)
     (*     parameters: {G A B u v}, *)
     (*       eqtype G A B -> *)
     (*       eqterm G u v Empty -> *)
     (*       eqterm G *)
     (*              (exfalso A u) *)
     (*              (exfalso B v) *)
     (*              A *)

     | CongCond :
       whenBoolType rule
         parameters: {G C1 C2 u1 u2 v1 v2 w1 w2},
         precond: isctx G
         precond: istype (ctxextend G Bool) C1
         precond: istype (ctxextend G Bool) C2
         precond: isterm G u1 Bool
         precond: isterm G u2 Bool
         precond: isterm G v1 (Subst C1 (sbzero Bool true))
         precond: isterm G v2 (Subst C1 (sbzero Bool true))
         precond: isterm G w1 (Subst C1 (sbzero Bool false))
         precond: isterm G w2 (Subst C1 (sbzero Bool false))
         premise: eqterm G u1 u2 Bool
         premise: eqtype (ctxextend G Bool) C1 C2
         premise: eqterm G v1 v2 (Subst C1 (sbzero Bool true))
         premise: eqterm G w1 w2 (Subst C1 (sbzero Bool false))
         conclusion:
           eqterm G
                  (cond C1 u1 v1 w1)
                  (cond C2 u2 v2 w2)
                  (Subst C1 (sbzero Bool u1))
       endrule

     | CongTermSubst :
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
       endrule

     | CongPair :
       whenBinaryProdType rule
         parameters: {G A1 A2 B1 B2 u1 u2 v1 v2},
         premise: eqterm G u1 u2 A1
         premise: eqterm G v1 v2 B1
         premise: eqtype G A1 A2
         premise: eqtype G B1 B2
         precond: isctx G
         precond: istype G A1
         precond: istype G A2
         precond: istype G B1
         precond: istype G B2
         precond: isterm G u1 A1
         precond: isterm G u2 A1
         precond: isterm G v1 B1
         precond: isterm G v2 B1
         conclusion:
           eqterm G
                  (pair A1 B1 u1 v1)
                  (pair A2 B2 u2 v2)
                  (BinaryProd A1 B1)
       endrule

     | CongProjOne :
       whenBinaryProdType rule
         parameters: {G A1 A2 B1 B2 p1 p2},
         premise: eqterm G p1 p2 (BinaryProd A1 B1)
         premise: eqtype G A1 A2
         premise: eqtype G B1 B2
         precond: isctx G
         precond: istype G A1
         precond: istype G A2
         precond: istype G B1
         precond: istype G B2
         precond: isterm G p1 (BinaryProd A1 B1)
         precond: isterm G p2 (BinaryProd A1 B1)
         conclusion:
           eqterm G
                  (proj1 A1 B1 p1)
                  (proj1 A2 B2 p2)
                  A1
       endrule

     | CongProjTwo :
       whenBinaryProdType rule
         parameters: {G A1 A2 B1 B2 p1 p2},
         premise: eqterm G p1 p2 (BinaryProd A1 B1)
         premise: eqtype G A1 A2
         premise: eqtype G B1 B2
         precond: isctx G
         precond: istype G A1
         precond: istype G A2
         precond: istype G B1
         precond: istype G B2
         precond: isterm G p1 (BinaryProd A1 B1)
         precond: isterm G p2 (BinaryProd A1 B1)
         conclusion:
           eqterm G
                  (proj2 A1 B1 p1)
                  (proj2 A2 B2 p2)
                  B1
       endrule

     | EqSubstPair :
       whenBinaryProdType rule
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
                  (BinaryProd (Subst A sbs) (Subst B sbs))
       endrule

     | EqSubstProjOne :
       whenBinaryProdType rule
         parameters: {G D A B p sbs},
         premise: issubst sbs G D
         premise: isterm D p (BinaryProd A B)
         precond: isctx G
         precond: isctx D
         precond: istype D A
         precond: istype D B
         conclusion:
           eqterm G
                  (subst (proj1 A B p) sbs)
                  (proj1 (Subst A sbs) (Subst B sbs) (subst p sbs))
                  (Subst A sbs)
       endrule

     | EqSubstProjTwo :
       whenBinaryProdType rule
         parameters: {G D A B p sbs},
         premise: issubst sbs G D
         premise: isterm D p (BinaryProd A B)
         precond: isctx G
         precond: isctx D
         precond: istype D A
         precond: istype D B
         conclusion:
           eqterm G
                  (subst (proj2 A B p) sbs)
                  (proj2 (Subst A sbs) (Subst B sbs) (subst p sbs))
                  (Subst B sbs)
       endrule

     | ProjOnePair :
       whenBinaryProdType rule
         parameters: {G A B u v},
         premise: isterm G u A
         premise: isterm G v B
         precond: isctx G
         precond: istype G A
         precond: istype G B
         conclusion:
           eqterm G
                  (proj1 A B (pair A B u v))
                  u
                  A
       endrule

     | ProjTwoPair :
       whenBinaryProdType rule
         parameters: {G A B u v},
         premise: isterm G u A
         premise: isterm G v B
         precond: isctx G
         precond: istype G A
         precond: istype G B
         conclusion:
           eqterm G
                  (proj2 A B (pair A B u v))
                  v
                  B
       endrule

     | PairEta :
       whenBinaryProdType rule
         parameters: {G A B p q},
         premise: eqterm G (proj1 A B p) (proj1 A B q) A
         premise: eqterm G (proj2 A B p) (proj2 A B q) B
         premise: isterm G p (BinaryProd A B)
         premise: isterm G q (BinaryProd A B)
         precond: isctx G
         precond: istype G A
         precond: istype G B
         conclusion:
           eqterm G p q (BinaryProd A B)
       endrule

     | CongEx :
       whenSumType rule
         parameters: {G A1 A2 B1 B2 a1 a2 b1 b2},
         premise: eqterm G a1 a2 A1
         premise: eqterm G b1 b2 (Subst B1 (sbzero A1 a1))
         premise: eqtype G A1 A2
         premise: eqtype (ctxextend G A1) B1 B2
         precond: isterm G a1 A1
         precond: isterm G a2 A1
         precond: isterm G b1 (Subst B1 (sbzero A1 a1))
         precond: isterm G b2 (Subst B2 (sbzero A2 a2))
         precond: istype G A1
         precond: istype G A2
         precond: istype (ctxextend G A1) B1
         precond: istype (ctxextend G A1) B2
         precond: isctx G
         conclusion:
           eqterm G (ex A1 B1 a1 b1) (ex A2 B2 a2 b2) (Sum A1 B1)
       endrule

     | CongSumElim :
       whenSumType rule
         parameters: {G A1 A2 B1 B2 C1 C2 p1 p2 c1 c2},
         premise: eqterm G p1 p2 (Sum A1 B1)
         premise: eqtype (ctxextend G (Sum A1 B1)) C1 C2
         premise: eqterm (ctxextend (ctxextend G A1) B1)
                         c1 c2
                         (Subst C1
                                (sbzero (Sum A1 B1) (ex A1 B1 (var 1) (var 0))))
         premise: eqtype G A1 A2
         premise: eqtype (ctxextend G A1) B1 B2
         precond: isterm G p1 (Sum A1 B1)
         precond: isterm G p2 (Sum A1 B1)
         precond: isterm (ctxextend (ctxextend G A1) B1)
                         c1
                         (Subst C1
                                (sbzero (Sum A1 B1) (ex A1 B1 (var 1) (var 0))))
         precond: isterm (ctxextend (ctxextend G A1) B1)
                         c2
                         (Subst C1
                                (sbzero (Sum A1 B1) (ex A1 B1 (var 1) (var 0))))
         precond: istype G A1
         precond: istype G A2
         precond: istype (ctxextend G A1) B1
         precond: istype (ctxextend G A1) B2
         precond: istype (ctxextend G (Sum A1 B1)) C1
         precond: istype (ctxextend G (Sum A1 B1)) C2
         precond: isctx G
         conclusion:
           eqterm G
                  (sumelim A1 B1 C1 p1 c1)
                  (sumelim A2 B2 C2 p2 c2)
                  (Subst C1 (sbzero (Sum A1 B1) p1))
       endrule

     | EqSubstEx :
       whenSumType rule
         parameters: {G D A B a b sbs},
         premise: issubst sbs G D
         premise: isterm D a A
         premise: isterm D b (Subst B (sbzero A a))
         precond: istype D A
         precond: istype (ctxextend D A) B
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst (ex A B a b) sbs)
                  (ex (Subst A sbs)
                      (Subst B (sbshift A sbs))
                      (subst a sbs)
                      (subst b sbs))
                  (Sum (Subst A sbs) (Subst B (sbshift A sbs)))
       endrule

     | EqSubstSumElim :
       whenSumType rule
         parameters: {G D A B C p c sbs},
         premise: issubst sbs G D
         premise: isterm D p (Sum A B)
         premise: istype (ctxextend D (Sum A B)) C
         premise:
           isterm (ctxextend (ctxextend D A) B)
                  c
                  (Subst C (sbzero (Sum A B) (ex A B (var 1) (var 0))))
         precond: istype D A
         precond: istype (ctxextend D A) B
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst (sumelim A B C p c) sbs)
                  (sumelim (Subst A sbs)
                           (Subst B (sbshift A sbs))
                           (Subst C (sbshift (Sum A B) sbs))
                           (subst p sbs)
                           (subst c sbs)
                  )
                  (Subst (Subst C (sbzero (Sum A B) p)) sbs)
       endrule

     | SumElimEx :
       whenSumType rule
         parameters: {G A B C a b c},
         premise: isterm G a A
         premise: isterm G b (Subst B (sbzero A a))
         premise: istype (ctxextend G (Sum A B)) C
         premise:
           isterm (ctxextend (ctxextend G A) B)
                  c
                  (Subst C (sbzero (Sum A B) (ex A B (var 1) (var 0))))
         precond: istype G A
         precond: istype (ctxextend G A) B
         precond: isctx G
         conclusion:
           eqterm G
                  (sumelim A B C (ex A B a b) c)
                  (subst (subst c (sbzero B b)) (sbzero A a))
                  (Subst C (sbzero (Sum A B) (ex A B a b)))
       endrule

     | EqSubstUniProd :
       whenUniverses whenProdType rule
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
       endrule

     | EqSubstUniProdProp :
       whenUniverses whenPropType whenProdType rule
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
       endrule

     | EqSubstUniId :
       whenUniverses whenIdType rule
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
       endrule

     | EqSubstUniEmpty :
       whenEmptyType whenUniverses rule
         parameters: {G D n sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst (uniEmpty n) sbs)
                  (uniEmpty n)
                  (Uni n)
       endrule

     | EqSubstUniUnit :
       whenUnitType whenUniverses rule
         parameters: {G D n sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst (uniUnit n) sbs)
                  (uniUnit n)
                  (Uni n)
       endrule

     | EqSubstUniBool :
       whenBoolType whenUniverses rule
         parameters: {G D n sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst (uniBool n) sbs)
                  (uniBool n)
                  (Uni (uni n))
       endrule

     | EqSubstUniBinaryProd :
       whenUniverses whenBinaryProdType rule
         parameters: {G D a b n m sbs},
         premise: issubst sbs G D
         premise: isterm D a (Uni (uni n))
         premise: isterm D b (Uni (uni m))
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst (uniBinaryProd (uni n) (uni m) a b) sbs)
                  (uniBinaryProd (uni n) (uni m) (subst a sbs) (subst b sbs))
                  (Uni (uni (max n m)))
       endrule

     | EqSubstUniBinaryProdProp :
       whenUniverses whenPropType whenBinaryProdType rule
         parameters: {G D a b sbs},
         premise: issubst sbs G D
         premise: isterm D a (Uni prop)
         premise: isterm D b (Uni prop)
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst (uniBinaryProd prop prop a b) sbs)
                  (uniBinaryProd prop prop (subst a sbs) (subst b sbs))
                  (Uni prop)
       endrule

     | EqSubstUniSum :
       whenUniverses whenSumType rule
         parameters: {G D a b n m sbs},
         premise: issubst sbs G D
         premise: isterm D a (Uni (uni n))
         premise: isterm (ctxextend D (El (uni n) a)) b (Uni (uni m))
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst (uniSum (uni n) (uni m) a b) sbs)
                  (uniSum (uni n)
                           (uni m)
                           (subst a sbs)
                           (subst b (sbshift (El (uni n) a) sbs)))
                  (Uni (uni (max n m)))
       endrule

     | EqSubstUniSumProp :
       whenUniverses whenPropType whenSumType rule
         parameters: {G D a b sbs},
         premise: issubst sbs G D
         premise: isterm D a (Uni prop)
         premise: isterm (ctxextend D (El prop a)) b (Uni prop)
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst (uniSum prop prop a b) sbs)
                  (uniSum prop prop
                           (subst a sbs)
                           (subst b (sbshift (El prop a) sbs)))
                  (Uni prop)
       endrule

     | EqSubstUniUni :
       whenUniverses rule
         parameters: {G D n sbs},
         premise: issubst sbs G D
         precond: isctx G
         precond: isctx D
         conclusion:
           eqterm G
                  (subst (uniUni (uni n)) sbs)
                  (uniUni (uni n))
                  (Uni (uni (S n)))
       endrule

     | EqSubstUniProp :
       whenUniverses whenPropType rule
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

     | CongUniProd :
       whenUniverses whenProdType rule
         parameters: {G a1 a2 b1 b2 n m},
         premise: eqterm G a1 a2 (Uni (uni n))
         premise: eqterm (ctxextend G (El (uni n) a1)) b1 b2 (Uni (uni m))
         precond: isterm G a1 (Uni (uni n))
         precond: isterm G a2 (Uni (uni n))
         precond: isterm (ctxextend G (El (uni n) a1)) b1 (Uni (uni m))
         precond: isterm (ctxextend G (El (uni n) a1)) b2 (Uni (uni m))
         precond: isctx G
         conclusion:
           eqterm G
                  (uniProd (uni n) (uni m) a1 b1)
                  (uniProd (uni n) (uni m) a2 b2)
                  (Uni (uni (max n m)))
       endrule

     | CongUniProdProp :
       whenUniverses whenPropType whenProdType rule
         parameters: {G a1 a2 b1 b2 l},
         premise: eqterm G a1 a2 (Uni l)
         premise: eqterm (ctxextend G (El l a1)) b1 b2 (Uni prop)
         precond: isterm G a1 (Uni l)
         precond: isterm G a2 (Uni l)
         precond: isterm (ctxextend G (El l a1)) b1 (Uni prop)
         precond: isterm (ctxextend G (El l a1)) b2 (Uni prop)
         precond: isctx G
         conclusion:
           eqterm G
                  (uniProd l prop a1 b1)
                  (uniProd l prop a2 b2)
                  (Uni prop)
       endrule

     | CongUniId :
       whenUniverses whenIdType rule
         parameters: {G a1 a2 u1 u2 v1 v2 n},
         premise: eqterm G a1 a2 (Uni n)
         premise: eqterm G u1 u2 (El n a1)
         premise: eqterm G v1 v2 (El n a1)
         precond: isterm G a1 (Uni n)
         precond: isterm G a2 (Uni n)
         precond: isterm G u1 (El n a1)
         precond: isterm G u2 (El n a1)
         precond: isterm G v1 (El n a1)
         precond: isterm G v2 (El n a2)
         precond: isctx G
         conclusion:
           eqterm G
                  (uniId n a1 u1 v1)
                  (uniId n a2 u2 v2)
                  (Uni n)
       endrule

     | CongUniBinaryProd :
       whenUniverses whenBinaryProdType rule
         parameters: {G a1 a2 b1 b2 n m},
         premise: eqterm G a1 a2 (Uni (uni n))
         premise: eqterm G b1 b2 (Uni (uni m))
         precond: isterm G a1 (Uni (uni n))
         precond: isterm G a2 (Uni (uni n))
         precond: isterm G b1 (Uni (uni m))
         precond: isterm G b2 (Uni (uni m))
         precond: isctx G
         conclusion:
           eqterm G
                  (uniBinaryProd (uni n) (uni m) a1 b1)
                  (uniBinaryProd (uni n) (uni m) a2 b2)
                  (Uni (uni (max n m)))
       endrule

     | CongUniBinaryProdProp :
       whenUniverses whenPropType whenBinaryProdType rule
         parameters: {G a1 a2 b1 b2},
         premise: eqterm G a1 a2 (Uni prop)
         premise: eqterm G b1 b2 (Uni prop)
         precond: isterm G a1 (Uni prop)
         precond: isterm G a2 (Uni prop)
         precond: isterm G b1 (Uni prop)
         precond: isterm G b2 (Uni prop)
         precond: isctx G
         conclusion:
           eqterm G
                  (uniBinaryProd prop prop a1 b1)
                  (uniBinaryProd prop prop a2 b2)
                  (Uni prop)
       endrule

     | CongUniSum :
       whenUniverses whenSumType rule
         parameters: {G a1 a2 b1 b2 n m},
         premise: eqterm G a1 a2 (Uni (uni n))
         premise: eqterm (ctxextend G (El (uni n) a1)) b1 b2 (Uni (uni m))
         precond: isterm G a1 (Uni (uni n))
         precond: isterm G a2 (Uni (uni n))
         precond: isterm (ctxextend G (El (uni n) a1)) b1 (Uni (uni m))
         precond: isterm (ctxextend G (El (uni n) a1)) b2 (Uni (uni m))
         precond: isctx G
         conclusion:
           eqterm G
                  (uniSum (uni n) (uni m) a1 b1)
                  (uniSum (uni n) (uni m) a2 b2)
                  (Uni (uni (max n m)))
       endrule

     | CongUniSumProp :
       whenUniverses whenPropType whenSumType rule
         parameters: {G a1 a2 b1 b2},
         premise: eqterm G a1 a2 (Uni prop)
         premise: eqterm (ctxextend G (El prop a1)) b1 b2 (Uni prop)
         precond: isterm G a1 (Uni prop)
         precond: isterm G a2 (Uni prop)
         precond: isterm (ctxextend G (El prop a1)) b1 (Uni prop)
         precond: isterm (ctxextend G (El prop a1)) b2 (Uni prop)
         precond: isctx G
         conclusion:
           eqterm G
                  (uniSum prop prop a1 b1)
                  (uniSum prop prop a2 b2)
                  (Uni prop)
       endrule
.

End TypeTheoryRules.

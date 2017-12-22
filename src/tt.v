(* Confgurable type theory. *)

(* Requirements:

   1. Use only letters (no numerals) in rule names, because we define LaTeX
      macros out of them, and those cannot contain numerals.

   2. Do not nest comments inside comments, or else the Python script will
      break.

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

     | TyUni :
       whenUniverses rule
         parameters: {G l},
         premise: isctx G
         conclusion:
           istype G (Uni l)
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

     | TermVarZero :
       rule
         parameters: {G A},
         precond: isctx G
         premise: istype G A
         conclusion:
           isterm (ctxextend G A) (var 0) A[sbweak]
       endrule

     | TermVarSucc :
       rule
         parameters: {G A B k},
         precond: isctx G
         precond: istype G A
         premise: isterm G (var k) A
         premise: istype G B
         conclusion:
           isterm (ctxextend G B) (var (S k)) A[sbweak]
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
           isterm G (app u A B v) B[v ⋅ sbid]
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
                (Id A[sbweak] u[sbweak] (var 0))
             )
             C
         premise:
           isterm G
                  w
                  C[u ⋅ refl A u ⋅ sbid]
         premise: isterm G v A
         premise: isterm G p (Id A u v)
         conclusion:
           isterm G
                  (j A u C w v p)
                  C[v ⋅ p ⋅ sbid]
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
         premise: isterm G v C[true ⋅ sbid]
         premise: isterm G w C[false ⋅ sbid]
         conclusion:
           isterm G (cond C u v w) C[u ⋅ sbid]
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
         parameters: {G l},
         premise: isctx G
         conclusion:
           isterm G (uniEmpty l) (Uni l)
       endrule

     | TermUniUnit :
       whenUnitType whenUniverses rule
         parameters: {G l},
         premise: isctx G
         conclusion:
           isterm G (uniUnit l) (Uni l)
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

     | TermUniBinaryProdProp :
       whenUniverses whenPropType whenBinaryProdType rule
         parameters: {G a b},
         premise: isterm G a (Uni prop)
         premise: isterm G b (Uni prop)
         precond: isctx G
         conclusion:
           isterm G (uniBinaryProd prop prop a b) (Uni prop)
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
                  u[v ⋅ sbid]
                  B[v ⋅ sbid]
       endrule

     | CondTrue :
       whenBoolType rule
         parameters: {G C v w},
         precond: isctx G
         premise: istype (ctxextend G Bool) C
         premise: isterm G v C[true ⋅ sbid]
         premise: isterm G w C[false ⋅ sbid]
         conclusion:
           eqterm G
                  (cond C true v w)
                  v
                  C[true ⋅ sbid]
       endrule

     | CondFalse :
       whenBoolType rule
         parameters: {G C v w},
         precond: isctx G
         premise: istype (ctxextend G Bool) C
         premise: isterm G v C[true ⋅ sbid]
         premise: isterm G w C[false ⋅ sbid]
         conclusion:
           eqterm G
                  (cond C false v w)
                  w
                  C[false ⋅ sbid]
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
                         (app u[sbweak] A[sbweak] B[var 0 ⋅ sbweak] (var 0))
                         (app v[sbweak] A[sbweak] B[var 0 ⋅ sbweak] (var 0))
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
                (Id A[sbweak] u[sbweak] (var 0)))
             C
         premise: isterm G w C[refl A u ⋅ u ⋅ sbid]
         conclusion:
           eqterm G
                  (j A u C w u (refl A u))
                  w
                  C[refl A u ⋅ u ⋅ sbid]
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
                  A2[u2 ⋅ sbid]
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
                (Id A1[sbweak] u1[sbweak] (var 0))
             )
             C1
         precond:
           istype
             (ctxextend
                (ctxextend G A1)
                (Id A1[sbweak] u1[sbweak] (var 0))
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
               (ctxextend (ctxextend G A1) (Id A1[sbweak] u1[sbweak] (var 0)))
               C1
               C2
         precond: isterm G w1 C1[refl A1 u1 ⋅ u1 ⋅ sbid]
         precond: isterm G w2 C1[refl A1 u1 ⋅ u1 ⋅ sbid]
         premise: eqterm G w1 w2 C1[refl A1 u1 ⋅ u1 ⋅ sbid]
         premise: eqterm G v1 v2 A1
         premise: eqterm G p1 p2 (Id A1 u1 v1)
         conclusion:
           eqterm G
                  (j A1 u1 C1 w1 v1 p1)
                  (j A2 u2 C2 w2 v2 p2)
                  C1[p1 ⋅ v1 ⋅ sbid]
       endrule

     | CongExfalso :
       whenEmptyType rule
         parameters: {G A B u v},
         premise: eqtype G A B
         premise: eqterm G u v Empty
         precond: isterm G u Empty
         precond: isterm G v Empty
         precond: istype G A
         precond: istype G B
         precond: isctx G
         conclusion:
           eqterm G
                  (exfalso A u)
                  (exfalso B v)
                  A
       endrule

     | CongCond :
       whenBoolType rule
         parameters: {G C1 C2 u1 u2 v1 v2 w1 w2},
         precond: isctx G
         precond: istype (ctxextend G Bool) C1
         precond: istype (ctxextend G Bool) C2
         precond: isterm G u1 Bool
         precond: isterm G u2 Bool
         precond: isterm G v1 C1[true ⋅ sbid]
         precond: isterm G v2 C1[true ⋅ sbid]
         precond: isterm G w1 C1[false ⋅ sbid]
         precond: isterm G w2 C1[false ⋅ sbid]
         premise: eqterm G u1 u2 Bool
         premise: eqtype (ctxextend G Bool) C1 C2
         premise: eqterm G v1 v2 C1[true ⋅ sbid]
         premise: eqterm G w1 w2 C1[false ⋅ sbid]
         conclusion:
           eqterm G
                  (cond C1 u1 v1 w1)
                  (cond C2 u2 v2 w2)
                  C1[u1 ⋅ sbid]
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
.

End TypeTheoryRules.

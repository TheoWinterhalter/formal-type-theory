Class Flag (A : Type) := {
  flagProof : A
}.

Class Syntax := {
  context      : Type ;
  type         : Type ;
  term         : Type ;
  substitution : Type ;

  (* Context constructors *)
  ctxempty  : context ;
  ctxextend : context -> type -> context ;

  (* Types *)
  Id    : type -> term -> term -> type ;
  Subst : type -> substitution -> type ;

  (* Terms *)
  var   : nat -> term ;
  refl  : type -> term -> term ;
  subst : term -> substitution -> term ;

  (* Explicit substitutions *)
  sbzero  : type -> term -> substitution ;
  sbweak  : type -> substitution ;
  sbshift : type -> substitution -> substitution ;
  sbid    : substitution ;
  sbcomp  : substitution -> substitution -> substitution
}.

Class Precond := {
  precondFlag : Type
}.

Class Reflection := {
  reflectionFlag : Type
}.

Class SimpleProducts `{Syntax} := {
  simpleproductsFlag : Type ;

  (* Type *)
  SimProd : forall {_ : Flag simpleproductsFlag}, type -> type -> type ;

  (* Terms *)
  pair  : forall {_ : Flag simpleproductsFlag}, type -> type -> term -> term -> term ;
  proj1 : forall {_ : Flag simpleproductsFlag}, type -> type -> term -> term ;
  proj2 : forall {_ : Flag simpleproductsFlag}, type -> type -> term -> term
}.

Class ProdEta := {
  prodetaFlag : Type
}.

Class WithJ `{Syntax} := {
  withjFlag : Type ;

  (* Term *)
  j : forall {_ : Flag withjFlag}, type -> term -> type -> term -> term -> term -> term
}.

Class WithEmpty `{Syntax} := {
  withemptyFlag : Type ;

  (* Type *)
  Empty : forall {_ : Flag withemptyFlag}, type ;

  (* Term *)
  exfalso : forall {_ : Flag withemptyFlag}, type -> term -> term
}.

Class WithUnit `{Syntax} := {
  withunitFlag : Type ;

  (* Type *)
  Unit : forall {_ : Flag withunitFlag}, type ;

  (* Term *)
  unit : forall {_ : Flag withunitFlag}, term
}.

Class WithBool `{Syntax} := {
  withboolFlag : Type ;

  (* Type *)
  Bool : forall {_ : Flag withboolFlag}, type ;

  (* Terms *)
  true  : forall {_ : Flag withboolFlag}, term ;
  false : forall {_ : Flag withboolFlag}, term ;
  cond  : forall {_ : Flag withboolFlag}, type -> term -> term -> term -> term
}.

Class WithPi `{Syntax} := {
  withpiFlag : Type ;

  (* Type *)
  Prod : forall {_ : Flag withpiFlag}, type -> type -> type ;

  (* Terms *)
  lam : forall {_ : Flag withpiFlag}, type -> type -> term -> term ;
  app : forall {_ : Flag withpiFlag}, term -> type -> type -> term -> term
}.

Class UniverseLevels := {
  level : Type
}.

Class Universes `{Syntax} `{UniverseLevels} := {
  universesFlag : Type ;

  (* Levels *)
  uni : forall {_ : Flag universesFlag}, nat -> level ;

  (* Types *)
  Uni : forall {_ : Flag universesFlag}, level -> type ;
  El  : forall {_ : Flag universesFlag}, level -> term -> type ;

  (* Terms *)
  uniUni : forall {_ : Flag universesFlag}, level -> term
}.

Class WithProp `{Universes} := {
  withpropFlag : Type ;

  (* Level *)
  prop : forall {_ : Flag withpropFlag}, level
}.

Class UniProd `{Universes} `{WithPi} := {
  uniProd : forall {_ : Flag universesFlag}, forall {_ : Flag withpiFlag},
            level -> level -> term -> term -> term
}.

Class UniId `{Universes} (* `{WithId} *) := {
  uniId : forall {_ : Flag universesFlag}, (* forall {_ : Flag withidFlag}, *)
          level -> term -> term -> term -> term
}.

Class UniEmpty `{Universes} `{WithEmpty} := {
  uniEmpty : forall {_ : Flag universesFlag}, forall {_ : Flag withemptyFlag},
             level -> term
}.

Class UniUnit `{Universes} `{WithUnit} := {
  uniUnit : forall {_ : Flag universesFlag}, forall {_ : Flag withunitFlag},
             level -> term
}.

Class UniBool `{Universes} `{WithBool} := {
  uniBool : forall {_ : Flag universesFlag}, forall {_ : Flag withboolFlag},
             nat -> term
}.

Class UniSimProd `{Universes} `{SimpleProducts} := {
  uniSimProd : forall {_ : Flag universesFlag}, forall {_ : Flag simpleproductsFlag},
               level -> level -> term -> term -> term
}.

Inductive Yes : Type := yes.
Inductive No : Type := .

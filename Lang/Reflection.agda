-- A modified copy of "agda/src/data/lib/prim/Agda/Builtin/Reflection.agda" from the Agda repository (https://github.com/agda/agda.git) at 2020-05-12 04:05 (commit bc8feec71e61a4c4369aa0ee93b77bf027c0f7f1).
-- The names here must be redefined because this project binds its custom builtin data types.
module Lang.Reflection where

open import Data.Boolean
open import Data.List
open import Data
open import Float
import      Lvl
open import FFI.MachineWord
open import Numeral.Natural
open import String
-- open import Agda.Builtin.Int
open import Type.Dependent
open import Type

-- Names --

postulate Name : TYPE
{-# BUILTIN QNAME Name #-}

primitive
  primQNameEquality : Name → Name → Bool
  primQNameLess     : Name → Name → Bool
  primShowQName     : Name → String

-- Fixity --

data Associativity : TYPE where
  left-assoc  : Associativity
  right-assoc : Associativity
  non-assoc   : Associativity

data Precedence : TYPE where
  related   : Float → Precedence
  unrelated : Precedence

data Fixity : TYPE where
  fixity : Associativity → Precedence → Fixity

{-# BUILTIN ASSOC      Associativity #-}
{-# BUILTIN ASSOCLEFT  left-assoc    #-}
{-# BUILTIN ASSOCRIGHT right-assoc   #-}
{-# BUILTIN ASSOCNON   non-assoc     #-}

{-# BUILTIN PRECEDENCE    Precedence #-}
{-# BUILTIN PRECRELATED   related    #-}
{-# BUILTIN PRECUNRELATED unrelated  #-}

{-# BUILTIN FIXITY       Fixity #-}
{-# BUILTIN FIXITYFIXITY fixity #-}

{-# COMPILE GHC Associativity = data MAlonzo.RTE.Assoc (MAlonzo.RTE.LeftAssoc | MAlonzo.RTE.RightAssoc | MAlonzo.RTE.NonAssoc) #-}
{-# COMPILE GHC Precedence    = data MAlonzo.RTE.Precedence (MAlonzo.RTE.Related | MAlonzo.RTE.Unrelated) #-}
{-# COMPILE GHC Fixity        = data MAlonzo.RTE.Fixity (MAlonzo.RTE.Fixity) #-}

{-# COMPILE JS Associativity  = function (x,v) { return v[x](); } #-}
{-# COMPILE JS left-assoc     = "left-assoc"  #-}
{-# COMPILE JS right-assoc    = "right-assoc" #-}
{-# COMPILE JS non-assoc      = "non-assoc"   #-}

{-# COMPILE JS Precedence     =
  function (x,v) {
    if (x === "unrelated") { return v[x](); } else { return v["related"](x); }} #-}
{-# COMPILE JS related        = function(x) { return x; } #-}
{-# COMPILE JS unrelated      = "unrelated"               #-}

{-# COMPILE JS Fixity         = function (x,v) { return v["fixity"](x["assoc"], x["prec"]); } #-}
{-# COMPILE JS fixity         = function (x) { return function (y) { return { "assoc": x, "prec": y}; }; } #-}

primitive
  primQNameFixity : Name → Fixity
  primQNameToWord64s : Name → Σ Word64 (λ _ → Word64)

-- Metavariables --

postulate Meta : TYPE
{-# BUILTIN AGDAMETA Meta #-}

primitive
  primMetaEquality : Meta → Meta → Bool
  primMetaLess     : Meta → Meta → Bool
  primShowMeta     : Meta → String
  primMetaToNat    : Meta → ℕ

-- Arguments --

-- Arguments can be (visible), {hidden}, or {{instance}}.
data Visibility : TYPE where
  visible hidden instance′ : Visibility

{-# BUILTIN HIDING   Visibility #-}
{-# BUILTIN VISIBLE  visible    #-}
{-# BUILTIN HIDDEN   hidden     #-}
{-# BUILTIN INSTANCE instance′  #-}

-- Arguments can be relevant or irrelevant.
data Relevance : TYPE where
  relevant irrelevant : Relevance

{-# BUILTIN RELEVANCE  Relevance  #-}
{-# BUILTIN RELEVANT   relevant   #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

data ArgInfo : TYPE where
  arg-info : (v : Visibility) (r : Relevance) → ArgInfo

data Arg {a} (A : TYPE a) : TYPE a where
  arg : (i : ArgInfo) (x : A) → Arg A

{-# BUILTIN ARGINFO    ArgInfo  #-}
{-# BUILTIN ARGARGINFO arg-info #-}
{-# BUILTIN ARG        Arg      #-}
{-# BUILTIN ARGARG     arg      #-}

-- Name abstraction --

data Abs {a} (A : TYPE a) : TYPE a where
  abs : (s : String) (x : A) → Abs A

{-# BUILTIN ABS    Abs #-}
{-# BUILTIN ABSABS abs #-}

-- Literals --

data Literal : TYPE where
  nat    : (n : ℕ)      → Literal
  word64 : (n : Word64) → Literal
  float  : (x : Float)  → Literal
  char   : (c : Char)   → Literal
  string : (s : String) → Literal
  name   : (x : Name)   → Literal
  meta   : (x : Meta)   → Literal

{-# BUILTIN AGDALITERAL   Literal #-}
{-# BUILTIN AGDALITNAT    nat     #-}
{-# BUILTIN AGDALITWORD64 word64  #-}
{-# BUILTIN AGDALITFLOAT  float   #-}
{-# BUILTIN AGDALITCHAR   char    #-}
{-# BUILTIN AGDALITSTRING string  #-}
{-# BUILTIN AGDALITQNAME  name    #-}
{-# BUILTIN AGDALITMETA   meta    #-}

-- Patterns --

data Pattern : TYPE where
  con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
  dot    : Pattern
  var    : (s : String)  → Pattern
  lit    : (l : Literal) → Pattern
  proj   : (f : Name)    → Pattern
  absurd : Pattern

{-# BUILTIN AGDAPATTERN   Pattern #-}
{-# BUILTIN AGDAPATCON    con     #-}
{-# BUILTIN AGDAPATLIT    lit     #-}
{-# BUILTIN AGDAPATPROJ   proj    #-}
{-# BUILTIN AGDAPATABSURD absurd  #-}

-- Terms --

data Sort   : TYPE
data Clause : TYPE
data Term   : TYPE
TypeTerm = Term

data Term where
  var       : (x : ℕ) (args : List (Arg Term)) → Term
  con       : (c : Name) (args : List (Arg Term)) → Term
  def       : (f : Name) (args : List (Arg Term)) → Term
  lam       : (v : Visibility) (t : Abs Term) → Term
  pat-lam   : (cs : List Clause) (args : List (Arg Term)) → Term
  pi        : (a : Arg TypeTerm) (b : Abs TypeTerm) → Term
  agda-sort : (s : Sort) → Term
  lit       : (l : Literal) → Term
  meta      : (x : Meta) → List (Arg Term) → Term
  unknown   : Term

data Sort where
  set     : (t : Term) → Sort
  lit     : (n : ℕ) → Sort
  unknown : Sort

data Clause where
  clause        : (ps : List (Arg Pattern)) (t : Term) → Clause
  absurd-clause : (ps : List (Arg Pattern)) → Clause

{-# BUILTIN AGDASORT    Sort   #-}
{-# BUILTIN AGDATERM    Term   #-}
{-# BUILTIN AGDACLAUSE  Clause #-}

{-# BUILTIN AGDATERMVAR         var       #-}
{-# BUILTIN AGDATERMCON         con       #-}
{-# BUILTIN AGDATERMDEF         def       #-}
{-# BUILTIN AGDATERMMETA        meta      #-}
{-# BUILTIN AGDATERMLAM         lam       #-}
{-# BUILTIN AGDATERMEXTLAM      pat-lam   #-}
{-# BUILTIN AGDATERMPI          pi        #-}
{-# BUILTIN AGDATERMSORT        agda-sort #-}
{-# BUILTIN AGDATERMLIT         lit       #-}
{-# BUILTIN AGDATERMUNSUPPORTED unknown   #-}

{-# BUILTIN AGDASORTSET         set     #-}
{-# BUILTIN AGDASORTLIT         lit     #-}
{-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

-- Definitions --

data Definition : TYPE where
  function    : (cs : List Clause) → Definition
  data-type   : (pars : ℕ) (cs : List Name) → Definition
  record-type : (c : Name) (fs : List (Arg Name)) → Definition
  data-cons   : (d : Name) → Definition
  axiom       : Definition
  prim-fun    : Definition

{-# BUILTIN AGDADEFINITION                Definition  #-}
{-# BUILTIN AGDADEFINITIONFUNDEF          function    #-}
{-# BUILTIN AGDADEFINITIONDATADEF         data-type   #-}
{-# BUILTIN AGDADEFINITIONRECORDDEF       record-type #-}
{-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-cons   #-}
{-# BUILTIN AGDADEFINITIONPOSTULATE       axiom       #-}
{-# BUILTIN AGDADEFINITIONPRIMITIVE       prim-fun    #-}

-- Errors --

data ErrorPart : TYPE where
  strErr  : String → ErrorPart
  termErr : Term → ErrorPart
  nameErr : Name → ErrorPart

{-# BUILTIN AGDAERRORPART       ErrorPart #-}
{-# BUILTIN AGDAERRORPARTSTRING strErr    #-}
{-# BUILTIN AGDAERRORPARTTERM   termErr   #-}
{-# BUILTIN AGDAERRORPARTNAME   nameErr   #-}

-- TC monad --

postulate
  TC               : ∀ {a} → TYPE a → TYPE a
  returnTC         : ∀ {a} {A : TYPE a} → A → TC A
  bindTC           : ∀ {a b} {A : TYPE a} {B : TYPE b} → TC A → (A → TC B) → TC B
  unify            : Term → Term → TC(Unit{Lvl.𝟎})
  typeError        : ∀ {a} {A : TYPE a} → List ErrorPart → TC A
  inferType        : Term → TC TypeTerm
  checkType        : Term → TypeTerm → TC Term
  normalise        : Term → TC Term
  reduce           : Term → TC Term
  catchTC          : ∀ {a} {A : TYPE a} → TC A → TC A → TC A
  quoteTC          : ∀ {a} {A : TYPE a} → A → TC Term
  unquoteTC        : ∀ {a} {A : TYPE a} → Term → TC A
  quoteωTC         : ∀ {A : Typeω} → A → TC Term
  getContext       : TC (List (Arg TypeTerm))
  extendContext    : ∀ {a} {A : TYPE a} → Arg TypeTerm → TC A → TC A
  inContext        : ∀ {a} {A : TYPE a} → List (Arg TypeTerm) → TC A → TC A
  freshName        : String → TC Name
  declareDef       : Arg Name → TypeTerm → TC(Unit{Lvl.𝟎})
  declarePostulate : Arg Name → TypeTerm → TC(Unit{Lvl.𝟎})
  defineFun        : Name → List Clause → TC(Unit{Lvl.𝟎})
  getType          : Name → TC TypeTerm
  getDefinition    : Name → TC Definition
  blockOnMeta      : ∀ {a} {A : TYPE a} → Meta → TC A
  commitTC         : TC(Unit{Lvl.𝟎})
  isMacro          : Name → TC Bool

  -- If the argument is 'true' makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : ∀ {a} {A : TYPE a} → Bool → TC A → TC A

  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String → ℕ → List ErrorPart → TC(Unit{Lvl.𝟎})

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
  noConstraints : ∀ {a} {A : TYPE a} → TC A → TC A

  -- Run the given TC action and return the first component. Resets to
  -- the old TC state if the second component is 'false', or keep the
  -- new TC state if it is 'true'.
  runSpeculative : ∀ {a} {A : TYPE a} → TC (Σ A λ _ → Bool) → TC A

{-# BUILTIN AGDATCM                           TC                         #-}
{-# BUILTIN AGDATCMRETURN                     returnTC                   #-}
{-# BUILTIN AGDATCMBIND                       bindTC                     #-}
{-# BUILTIN AGDATCMUNIFY                      unify                      #-}
{-# BUILTIN AGDATCMTYPEERROR                  typeError                  #-}
{-# BUILTIN AGDATCMINFERTYPE                  inferType                  #-}
{-# BUILTIN AGDATCMCHECKTYPE                  checkType                  #-}
{-# BUILTIN AGDATCMNORMALISE                  normalise                  #-}
{-# BUILTIN AGDATCMREDUCE                     reduce                     #-}
{-# BUILTIN AGDATCMCATCHERROR                 catchTC                    #-}
{-# BUILTIN AGDATCMQUOTETERM                  quoteTC                    #-}
{-# BUILTIN AGDATCMUNQUOTETERM                unquoteTC                  #-}
-- {-# BUILTIN AGDATCMQUOTEOMEGATERM             quoteωTC                   #-}
{-# BUILTIN AGDATCMGETCONTEXT                 getContext                 #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT              extendContext              #-}
{-# BUILTIN AGDATCMINCONTEXT                  inContext                  #-}
{-# BUILTIN AGDATCMFRESHNAME                  freshName                  #-}
{-# BUILTIN AGDATCMDECLAREDEF                 declareDef                 #-}
{-# BUILTIN AGDATCMDECLAREPOSTULATE           declarePostulate           #-}
{-# BUILTIN AGDATCMDEFINEFUN                  defineFun                  #-}
{-# BUILTIN AGDATCMGETTYPE                    getType                    #-}
{-# BUILTIN AGDATCMGETDEFINITION              getDefinition              #-}
{-# BUILTIN AGDATCMBLOCKONMETA                blockOnMeta                #-}
{-# BUILTIN AGDATCMCOMMIT                     commitTC                   #-}
{-# BUILTIN AGDATCMISMACRO                    isMacro                    #-}
{-# BUILTIN AGDATCMWITHNORMALISATION          withNormalisation          #-}
{-# BUILTIN AGDATCMDEBUGPRINT                 debugPrint                 #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS              noConstraints              #-}
{-# BUILTIN AGDATCMRUNSPECULATIVE             runSpeculative             #-}

module DoNotation where
  open import Syntax.Do

  instance
    TC-doNotation : ∀{ℓ} → DoNotation{ℓ}(TC)
    return ⦃ TC-doNotation ⦄ = returnTC
    _>>=_  ⦃ TC-doNotation ⦄ = bindTC

module Formalization.PrimitiveRecursion where

import      Lvl
open import Data
open import Data.ListSized
open import Numeral.Finite
open import Numeral.Natural
open import Syntax.Number
open import Type{Lvl.𝟎}

-- Function(n) is a syntactic representation of primitive recursive functions of type (ℕⁿ → ℕ).
-- The syntax
data Function : ℕ → Type where
  -- Base cases
  Base        : Function(0)
  Successor   : Function(1)
  Projection  : ∀{n : ℕ} → (i : 𝕟(n)) → Function(n)

  -- Inductive cases
  Composition : ∀{m n : ℕ} → Function(n) → List(Function(m))(n) → Function(m)
  Recursion   : ∀{n : ℕ} → Function(n) → Function(𝐒(𝐒(n))) → Function(𝐒(n))

Primitive : Type
Primitive = ℕ

module _ where
  open import Data.ListSized.Functions
  open import Functional

  private variable m n   : ℕ
  private variable i     : 𝕟(n)
  private variable x v   : Primitive
  private variable xs vs : List(Primitive)(n)
  private variable f g   : Function(m)
  private variable fs gs : List(Function(m))(n)

  -- The operational semantics.
  data _$_⟹_ : ∀{m n} → List(Function(m))(n) → List(Primitive)(m) → List(Primitive)(n) → Type
  data _$_⟶_ : ∀{n} → Function(n) → List(Primitive)(n) → ℕ → Type where
    zero : (Base $ ∅ ⟶ 𝟎)
    succ : (Successor $ singleton(n) ⟶ 𝐒(n))
    proj : (Projection{n}(i) $ xs ⟶ index(i)(xs))
    comp : (f $ vs ⟶ v) → (gs $ xs ⟹ vs) → (Composition{m}{n} f gs $ xs ⟶ v)
    rec𝟎 : (f $ xs ⟶ v) → (Recursion f g $ (𝟎 ⊰ xs) ⟶ v)
    rec𝐒 : (Recursion f g $ (n ⊰ xs) ⟶ x) → (g $ (n ⊰ x ⊰ xs) ⟶ v) → (Recursion f g $ (𝐒(n) ⊰ xs) ⟶ v)
  data _$_⟹_ where
    base : (∅ $ xs ⟹ ∅)
    step : (f $ xs ⟶ v) → (fs $ xs ⟹ vs) → ((f ⊰ fs) $ xs ⟹ (v ⊰ vs))

  -- Functionally equivalent to `evaluate f (map(g ↦ evaluate g xs)(gs))`, but the termination checker does not accept that form.
  mapEvaluate : ∀{m n} → List(Function(m))(n) → List(Primitive)(m) → List(Primitive)(n)

  -- The denotational semantics.
  -- This is possible to encode into an Agda function because: Primitive recursive functions ⊆ Agda functions.
  -- `Base` is interpreted as the constant 0.
  -- `Successor` is interpreted as the successor function of ℕ.
  -- `Projection{n}(i)` is interpreted as the projection of the i:th element of ℕⁿ.
  -- `Composition(f)(gs)` is interpreted as generalized composition by using map on the arguments of a function.
  --    Specifically (f ∘ (map gs)).
  -- `Recursion(f)(g)` is interpreted as a "recursion constructor".
  --    This is used to construct a function `r` in which the following holds:
  --    • r(0   ,..xs) = f(..xs)
  --    • r(𝐒(n),..xs) = g(n,r(n,..xs),..xs)
  {-# TERMINATING #-} -- TODO: Terminated before but the termination checker in Agda version 2.6.2-9bed10c denies this (or in some random cases it gives an internal error at src/full/Agda/TypeChecking/Reduce/Fast.hs:1358)
  evaluate : ∀{n} → Function(n) → (List(Primitive)(n) → Primitive)
  evaluate {.𝟎}   (Base)                     ∅             = 𝟎
  evaluate {.𝐒(𝟎)}(Successor)                (singleton x) = 𝐒(x)
  evaluate {_}    (Projection(i))            xs            = index(i)(xs)
  evaluate {m}    (Composition{m}{n}(f)(gs)) xs            = evaluate{n} f (mapEvaluate{m}{n} gs xs)
  evaluate {𝐒(_)} (Recursion(f)(g))          (𝟎    ⊰ xs)   = evaluate f xs
  evaluate {𝐒(m)} (Recursion(f)(g))          (𝐒(n) ⊰ xs)   = evaluate{𝐒(𝐒(m))} g (n ⊰ (evaluate{𝐒 m} (Recursion(f)(g)) (n ⊰ xs) ⊰ xs))

  mapEvaluate          ∅        xs = ∅
  mapEvaluate{m}{𝐒(n)} (g ⊰ gs) xs = (evaluate{m} g xs) ⊰ (mapEvaluate{m}{n} gs xs)

  ------------------------------------------------------
  -- This section proves the equivalence between the operational and the denotational semantics. Or it can be interpreted as the correctness of one of the definitions by the other one.
  -- This equivalence should be obvious from the definitions.
  --

  open import Relator.Equals
  open import Relator.Equals.Proofs
  open import Syntax.Transitivity

  [⟹]-to-eval : (fs $ xs ⟹ vs) → (mapEvaluate fs xs ≡ vs)

  [⟶]-to-eval : (f $ xs ⟶ v) → (evaluate f xs ≡ v)
  [⟶]-to-eval zero = [≡]-intro
  [⟶]-to-eval succ = [≡]-intro
  [⟶]-to-eval {xs = _⊰_ {𝟎}   x xs} (proj {i = 𝟎})   = [≡]-intro
  [⟶]-to-eval {xs = _⊰_ {𝐒 n} x xs} (proj {i = 𝟎})   = [≡]-intro
  [⟶]-to-eval {xs = _⊰_ {𝐒 n} x xs} (proj {i = 𝐒 i}) = [≡]-intro
  [⟶]-to-eval (comp p q) with [⟶]-to-eval p | [⟹]-to-eval q
  ... | [≡]-intro | [≡]-intro = [≡]-intro
  [⟶]-to-eval (rec𝟎 p) with [⟶]-to-eval p
  ... | [≡]-intro = [≡]-intro
  [⟶]-to-eval (rec𝐒 p q) with [⟶]-to-eval p | [⟶]-to-eval q
  ... | [≡]-intro | [≡]-intro = [≡]-intro
  [⟹]-to-eval {fs = ∅}      {vs = ∅}      _           = [≡]-intro
  [⟹]-to-eval {fs = f ⊰ fs} {vs = v ⊰ vs} (step p ps) with [⟶]-to-eval p | [⟹]-to-eval {fs = fs} {vs = vs} ps
  ... | [≡]-intro | [≡]-intro = [≡]-intro

  eval-to-[⟹] : (mapEvaluate fs xs ≡ vs) → (fs $ xs ⟹ vs)

  {-# TERMINATING #-} -- TODO: See TODO above in eval
  eval-to-[⟶] : (evaluate f xs ≡ v) → (f $ xs ⟶ v)
  eval-to-[⟶] {f = Base}             {∅}           [≡]-intro = zero
  eval-to-[⟶] {f = Successor}        {singleton x} [≡]-intro = succ
  eval-to-[⟶] {f = Projection _}                   [≡]-intro = proj
  eval-to-[⟶] {f = Composition f gs} {xs}          p         = comp (eval-to-[⟶] p) (eval-to-[⟹] [≡]-intro)
  eval-to-[⟶] {f = Recursion f g}    {𝟎    ⊰ xs}   p         = rec𝟎(eval-to-[⟶] {f = f}{xs = xs} p)
  eval-to-[⟶] {f = Recursion f g}    {𝐒(n) ⊰ xs}   p         = rec𝐒 (eval-to-[⟶] [≡]-intro) (eval-to-[⟶] p)

  eval-to-[⟹] {fs = ∅}      [≡]-intro = base
  eval-to-[⟹] {fs = f ⊰ fs} [≡]-intro = step (eval-to-[⟶] [≡]-intro) (eval-to-[⟹] [≡]-intro)

  -- TODO: Is it possible to prove that _⟶_ terminates and normalizes by using [⟶]-to-eval (total and deterministic)?

  open import Function.Equals
  open import Logic
  open import Logic.Predicate

  -- When a function on lists of primitives are primitive recursive.
  PrimitiveRecursive : (List(Primitive)(n) → Primitive) → Stmt
  PrimitiveRecursive(f) = ∃(e ↦ evaluate e ⊜ f)

Const : Function(0) → ∀{n} → Function(n)
Const(c) = Composition(c) ∅

-- TODO: Would encoding pairs make this easier to implement (e.g. the Cantor Pairing Function?
--  This is used to construct a function `r` in which the following holds for its evaluation:
--  • r(0      ,..xs) = f(..xs)
--  • r(1      ,..xs) = g(..xs)
--  • r(𝐒(𝐒(n)),..xs) = h(n,r(𝐒(n),..xs),r(n,..xs),..xs)
-- Recursion₂ : ∀{n : ℕ} → Function(n) → Function(n) → Function(𝐒(𝐒(𝐒(n)))) → Function(𝐒(n))
-- Recursion₂{n} (f)(g)(h) = Composition(Projection(0)) (Helper ⊰ ∅) where
--   Recursion
-- 
--   Helper : Function(2)
--   Helper = 
-- 

module Arithmetic where -- TODO: Prove that these are correct by `evaluate`
  Zero = Base

  Number : ℕ → Function(0)
  Number(𝟎)    = Zero
  Number(𝐒(n)) = Composition(Successor) (Number(n) ⊰ ∅)

  Swap₂ : Function(2) → Function(2)
  Swap₂(f) = Composition(f) (Projection(1) ⊰ Projection(0) ⊰ ∅)

  -- Addition (+) in ℕ.
  -- It describes the following function:
  --   evaluate(Addition)[𝟎   ,b] = 𝟎
  --   evaluate(Addition)[𝐒(a),b] = 𝐒(b)
  Addition : Function(2)
  Addition = Recursion(Projection(0)) (Composition Successor (Projection(1) ⊰ ∅))

  -- Multiplication (⋅) in ℕ.
  -- It describes the following function:
  --   evaluate(Multiplication)[𝟎   ,b] = 𝟎
  --   evaluate(Multiplication)[𝐒(a),b] = evaluate(Multiplication)[a,b] + b
  Multiplication : Function(2)
  Multiplication = Recursion (Const(Zero)) (Composition Addition (Projection(1) ⊰ Projection(2) ⊰ ∅))

  -- Exponentiation (^) in ℕ.
  -- It describes the following function:
  --   evaluate(Exponentiation)[a   ,0   ] = 1
  --   evaluate(Exponentiation)[a   ,𝐒(b)] = evaluate(Exponentiation)[a,b] ⋅ a
  Exponentiation : Function(2)
  Exponentiation = Swap₂(Recursion (Composition Successor (Const Zero ⊰ ∅)) (Composition Multiplication (Projection(1) ⊰ Projection(2) ⊰ ∅)))

  -- Factorial (!) in ℕ.
  -- It describes the following function:
  --   evaluate(Factorial)[𝟎   ] = 1
  --   evaluate(Factorial)[𝐒(a)] = 𝐒(a) ⋅ evaluate(Factorial)[a,b]
  Factorial : Function(1)
  Factorial = Recursion(Number(1)) (Composition Multiplication ((Composition Successor (Projection(0) ⊰ ∅)) ⊰ Projection(1) ⊰ ∅))

  -- Predecessor (𝐏) in ℕ.
  -- It describes the following function:
  --   evaluate(Predecessor)[𝟎   ] = 𝟎
  --   evaluate(Predecessor)[𝐒(a)] = a
  Predecessor : Function(1)
  Predecessor = Recursion(Zero) (Projection(0))

  -- Monus/Cut-off minus (−₀) in ℕ.
  -- It describes the following function:
  --   evaluate(Monus)[b,𝟎   ] = b
  --   evaluate(Monus)[b,𝐒(a)] = 𝐏(evaluate(Monus)[b,a])
  Monus : Function(2)
  Monus = Swap₂(Recursion(Projection(0)) (Composition Predecessor (Projection(1) ⊰ ∅)))

  -- Maximum (max) of ℕ² in ℕ.
  -- It describes the following function:
  --   evaluate(Max)[a,b] = a + (b −₀ a)
  Max : Function(2)
  Max = Composition(Addition) (Projection(0) ⊰ Swap₂(Monus) ⊰ ∅)

  -- Minimum (min) of ℕ² in ℕ.
  -- It describes the following function:
  --   evaluate(Min)[a,b] = (a + b) −₀ max(a,b)
  Min : Function(2)
  Min = Composition(Monus) (Addition ⊰ Max ⊰ ∅)

  -- It describes the following function:
  --   evaluate(Distance)[a,b] = max(x −₀ y , y −₀ x)
  Distance : Function(2)
  Distance = Composition(Addition) (Monus ⊰ Swap₂(Monus) ⊰ ∅)

  -- It describes the following function:
  --   evaluate(IsZero)[𝟎]    = 1
  --   evaluate(IsZero)[𝐒(_)] = 0
  IsZero : Function(1)
  IsZero = Recursion(Number(1)) (Const(Zero))

  -- It describes the following function:
  --   evaluate(IsZero)[𝟎]    = 0
  --   evaluate(IsZero)[𝐒(_)] = 1
  IsNonZero : Function(1)
  IsNonZero = Composition(IsZero) (IsZero ⊰ ∅)

  Eq : Function(2)
  Eq = Composition(IsZero) (Distance ⊰ ∅)

  -- It describes the following function:
  --   evaluate(Fibonacci)[𝟎]    = 0
  --   evaluate(Fibonacci)[𝐒(_)] = 1
  -- Fibonacci : Function(1)
  -- Fibonacci = Composition(Projection(0)) (Fib ⊰ ∅) where
  --   Fib : Function(2)
  --   Fib = 

-- TODO: http://www.reluctantm.com/gcruttw/teaching/cpsc513.W2010/A3Solutions.pdf
-- TODO: http://ii.fmph.uniba.sk/cl/courses/1-AIN-625-lpp/0910zs/ln/doc/ch_p_gd.pdf

module Proofs where
  open import Functional
  open import Logic.Propositional
  open import Numeral.Natural.Oper
  open import Numeral.Natural.Oper.Comparisons
  open import Numeral.Natural.Oper.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs
  open import Structure.Function using (congruence₁)
  open import Structure.Operator.Properties
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  addition-correctness : ∀{a b} → (evaluate Arithmetic.Addition (a ⊰ b ⊰ ∅) ≡ a + b)
  addition-correctness {𝟎}   {b} = [≡]-intro
  addition-correctness {𝐒 a} {b} = congruence₁(𝐒) (addition-correctness {a}{b})

  multiplication-correctness : ∀{a b} → (evaluate Arithmetic.Multiplication (a ⊰ b ⊰ ∅) ≡ a ⋅ b)
  multiplication-correctness {𝟎}   {b} = [≡]-intro
  multiplication-correctness {𝐒 a} {b} =
    addition-correctness {evaluate Arithmetic.Multiplication (a ⊰ b ⊰ ∅)}{b}
    🝖 congruence₁(_+ b) (multiplication-correctness {a}{b})
    🝖 symmetry(_≡_) ([⋅]-with-[𝐒]ₗ {a}{b})

  exponentiation-correctness : ∀{a b} → (evaluate Arithmetic.Exponentiation (a ⊰ b ⊰ ∅) ≡ a ^ b)
  exponentiation-correctness {a} {𝟎}   = [≡]-intro
  exponentiation-correctness {a} {𝐒 b} =
    multiplication-correctness {evaluate Arithmetic.Exponentiation (a ⊰ b ⊰ ∅)}{a}
    🝖 congruence₁(_⋅ a) (exponentiation-correctness {a}{b})
    🝖 commutativity(_⋅_) {a ^ b}{a}

  factorial-correctness : ∀{a} → (evaluate Arithmetic.Factorial (a ⊰ ∅) ≡ a !)
  factorial-correctness {𝟎}   = [≡]-intro
  factorial-correctness {𝐒 a} =
    multiplication-correctness {𝐒 a}
    🝖 congruence₁(𝐒(a) ⋅_) (factorial-correctness {a})

  predecessor-correctness : ∀{a} → (evaluate Arithmetic.Predecessor (a ⊰ ∅) ≡ 𝐏(a))
  predecessor-correctness {𝟎}   = [≡]-intro
  predecessor-correctness {𝐒 a} = [≡]-intro

  monus-correctness : ∀{a b} → (evaluate Arithmetic.Monus (a ⊰ b ⊰ ∅) ≡ a −₀ b)
  monus-correctness {a}   {𝟎}   = [≡]-intro
  monus-correctness {𝟎}   {𝐒 b} = predecessor-correctness{evaluate Arithmetic.Monus (𝟎 ⊰ b ⊰ ∅)} 🝖 congruence₁(𝐏) (monus-correctness {𝟎}{b})
  monus-correctness {𝐒 a} {𝐒 b} =
    predecessor-correctness{evaluate Arithmetic.Monus (𝐒(a) ⊰ b ⊰ ∅)}
    🝖 congruence₁(𝐏) (monus-correctness {𝐒 a}{b})
    🝖 symmetry(_≡_) ([−₀]-with-[𝐒]ᵣ {𝐒(a)}{b})

  isnonzero-correctness : ∀{a} → (evaluate Arithmetic.IsNonZero (a ⊰ ∅) ≡ ℕbool(a ≢? 𝟎))
  isnonzero-correctness {𝟎}   = [≡]-intro
  isnonzero-correctness {𝐒 a} = [≡]-intro

  iszero-correctness : ∀{a} → (evaluate Arithmetic.IsZero (a ⊰ ∅) ≡ ℕbool(a ≡? 𝟎))
  iszero-correctness {𝟎}   = [≡]-intro
  iszero-correctness {𝐒 a} = [≡]-intro

  -- TODO: Formalize "Function(1) is countably infinite". Maybe take some inspiration from https://proofwiki.org/wiki/Not_All_URM_Computable_Functions_are_Primitive_Recursive . Then prove that (ℕ → ℕ) is not countably infinite, and therefore not all computable functions are expressible primitive recursively (is this argument constructive?)

  open import Data.Tuple
  open import Function.Inverse
  open import Logic.Predicate
  open import Logic.Propositional
  open import Type.Size.Countable
  open import Structure.Function.Domain.Proofs
  open import Structure.Function using (congruence₁)
  open import Syntax.Function
  open import Syntax.Transitivity

  postulate Function-countablyInfinite : CountablyInfinite(Function(1))
  encodeFunction : Function(1) → ℕ
  encodeFunction = inv _ ⦃ bijective-to-invertible ⦃ bij = [∃]-proof Function-countablyInfinite ⦄ ⦄

  -- TODO: Use a lifted Numeral.Natural.Sequence.pairIndexing as a witness directly (instead of encodePair). Another alternative is (a ↦ b ↦ 2ᵃ⋅3ᵇ) if it is easier to construct f that way.
  postulate Function-value-pair-countablyInfinite : CountablyInfinite(Function(1) ⨯ ℕ)
  encodePair : (Function(1) ⨯ ℕ) → ℕ
  encodePair = inv _ ⦃ bijective-to-invertible ⦃ bij = [∃]-proof Function-value-pair-countablyInfinite ⦄ ⦄

  -- TODO: Is it possible to use Logic.DiagonalMethod for this proof?
  no-self-interpreter : ¬ ∃(interpret ↦ ∀{f}{n} → evaluate interpret (singleton (encodePair(f , n))) ≡ evaluate f (singleton n))
  no-self-interpreter ([∃]-intro interpret ⦃ p ⦄) = 𝐒-not-self(symmetry(_≡_) x) where
    postulate f : Function(1)
    postulate f-correctness : ∀{g} → (evaluate f (singleton(encodeFunction g)) ≡ encodePair(g , encodeFunction g))

    g : Function(1)
    g = Composition Successor (singleton (Composition interpret (singleton f)))

    x : evaluate g (singleton (encodeFunction g)) ≡ 𝐒(evaluate g (singleton (encodeFunction g)))
    x =
      evaluate g (singleton (encodeFunction g))                                   🝖[ _≡_ ]-[]
      𝐒(evaluate interpret (singleton(evaluate f (singleton(encodeFunction g))))) 🝖[ _≡_ ]-[ congruence₁(𝐒) (congruence₁(evaluate interpret) (congruence₁(singleton) f-correctness)) ]
      𝐒(evaluate interpret (singleton(encodePair(g , encodeFunction g))))         🝖[ _≡_ ]-[ congruence₁(𝐒) p ]
      𝐒(evaluate g (singleton(encodeFunction g)))                                 🝖-end

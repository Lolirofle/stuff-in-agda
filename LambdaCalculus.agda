module LambdaCalculus where

import      Lvl
open import Data
open import Data.Boolean
open import Data.Boolean.Operators
open import Logic.Propositional using (⊥ ; [⊥]-elim)
open import Logic.Predicate
open import Numeral.Natural
-- open import Numeral.Natural.Oper.Comparisons
open import Numeral.Finite
open import Numeral.Finite.Bound
open import Numeral.Finite.Oper
open import Numeral.Finite.Oper.Comparisons
open import Numeral.Finite.Oper.Comparisons.Proofs
open import Numeral.Natural.Function
open import Numeral.Natural.Oper renaming (_+_ to _+ₙ_)
open import Numeral.Natural.Oper.Proofs
open import Numeral.Natural.Relation.Order
open import Numeral.Natural.Relation.Order.Proofs
open import Numeral.Sign
open import Relator.Equals
open import Relator.Equals.Proofs
open import Syntax.Number

-- TODO: Someone else did something similiar apparently: https://gist.github.com/gallais/303cfcfe053fbc63eb61
-- TODO: Execution is possible, but limited? https://stackoverflow.com/questions/2583337/strictly-positive-in-agda#

-- A lambda term (A term in the language of lambda calculus).
-- This is encoded with an abstraction depth which ensures that every term is well-formed.
data Term : ℕ → Set where
  -- The term which represents applying the second term on the first term.
  -- Representation in function notation:
  --   (Apply f(x)) is f(x)
  Apply : ∀{d} → Term(d) → Term(d) → Term(d)

  -- The term which represents bounding a new variable (introducing a variable).
  -- Representation in function notation:
  --   (Abstract{n} term) is (xₙ ↦ term)
  Abstract : ∀{d} → Term(𝐒(d)) → Term(d)

  -- The term which represents a specific variable in scope.
  -- Representation in function notation:
  --   (Var(n)) is xₙ
  Var : ∀{d} → 𝕟(d) → Term(d)

Expression : Set
Expression = Term(0)

-- Syntax for writing Var as a numeral
instance
  Term-from-ℕ : ∀{N} → Numeral(Term(N))
  Numeral.restriction-ℓ ( Term-from-ℕ {N} ) = Numeral.restriction-ℓ ( 𝕟-from-ℕ {N} )
  Numeral.restriction   ( Term-from-ℕ {N} ) = Numeral.restriction ( 𝕟-from-ℕ {N} )
  num                   ⦃ Term-from-ℕ {N} ⦄ (n) ⦃ proof ⦄ = Var(num n)

module Transformations where
  -- Increase the depth level of the given term by something
  depth-[≤] : ∀{d₁ d₂} → ⦃ _ : (d₁ ≤ d₂) ⦄ → Term(d₁) → Term(d₂)
  depth-[≤] (Apply t1 t2) = Apply(depth-[≤] t1) (depth-[≤] t2)
  depth-[≤] (Abstract t) = Abstract(depth-[≤] t)
  depth-[≤] (Var x) = Var(bound-[≤] x)

  -- Increment the depth level of the given term by 1
  depth-𝐒 : ∀{d} → Term(d) → Term(𝐒(d))
  depth-𝐒 = depth-[≤]
  -- depth-𝐒 (Apply(f)(x))       = Apply (depth-𝐒(f)) (depth-𝐒(x))
  -- depth-𝐒 (Abstract(body))    = Abstract(depth-𝐒(body))
  -- depth-𝐒 (Var(n))            = Var(bound-𝐒 (n))

  -- Add to the depth level of the given term
  depth-[+] : ∀{d₁ d₂} → Term(d₁) → Term(d₁ +ₙ d₂)
  depth-[+] = depth-[≤] ⦃ [≤]-of-[+]ₗ ⦄
  -- depth-[+] {d₁}{d₂} (Apply(f)(x)) = Apply (depth-[+] {d₁}{d₂} (f)) (depth-[+] {d₁}{d₂} (x))
  -- depth-[+] {d₁}{d₂} (Abstract(body)) =
  --   (Abstract
  --     ([≡]-elimᵣ
  --       ([+1]-commutativity {d₁}{d₂})
  --       {Term}
  --       (depth-[+] {𝐒(d₁)}{d₂} (body))
  --     )
  --   )
  -- depth-[+] {d₁}{d₂} (Var(n)) = Var(bound-[+] {d₁}{d₂} (n))

  depth-max : ∀{d₁ d₂} → Term(d₁) → Term(max d₁ d₂)
  depth-max = depth-[≤] where
    import Numeral.Natural.Function.Proofs

  Apply₊ : ∀{d₁ d₂} → ⦃ _ : (d₁ ≤ d₂) ⦄ → Term(d₂) → Term(d₁) → Term(d₂)
  Apply₊ {d₁}{d₂} f(x) = Apply f(depth-[≤] {d₁}{d₂} (x))

  {-
  -- Increase all variables of the given term
  var-[≤] : ∀{d₁ d₂} → ⦃ _ : (d₁ ≤ d₂) ⦄ → Term(d₁) → Term(d₂)
  var-[≤] (Apply t1 t2) = Apply(depth-[≤] t1) (depth-[≤] t2)
  var-[≤] (Abstract t)  = Abstract(depth-[≤] t)
  var-[≤] (Var x) = Var({!x + (d₂ − d₁)!}) where
    open import Numeral.Natural.TotalOper
  -}

  -- Increment all variables of the given term
  var-𝐒 : ∀{d} → Term(d) → Term(𝐒(d))
  var-𝐒 (Apply(f)(x))       = Apply (var-𝐒(f)) (var-𝐒(x))
  var-𝐒 (Abstract{d}(body)) = Abstract{𝐒(d)}(var-𝐒(body))
  var-𝐒 (Var{𝐒(d)}(n))      = Var{𝐒(𝐒(d))}(𝐒(n))

  -- Add to all variables of the given term
  {-TODO: It worked before! Maybe an automatic merge failure? var-[+] : ∀{d₁ d₂} → 𝕟(d₂) → Term(d₁) → Term(d₁ + d₂)
  var-[+] {d₁}{𝟎}     ()
  var-[+] {d₁}{𝐒(d₂)} (n) (Apply (f) (x))        = Apply (var-[+] (n)(f)) (var-[+] (n)(x))
  var-[+] {d₁}{𝐒(d₂)} (n) (Abstract{.d₁} (body)) = Abstract (var-[+] (n)(body))
  var-[+] {d₁}{𝐒(d₂)} (n) (Var{𝟎} ())
  var-[+] {d₁}{𝐒(d₂)} (n) (Var{𝐒(_)} (v))        = Var{d₁ + 𝐒(d₂)} (v +ᶠ n)
-}

-- This module assumes that the semantics is the following:
-- • Var(0) is the variable that was first/furthest/(least recently) bounded.
module IndexZeroFurthest where
  open Transformations

  module OperSyntax where
    infixr 100 _↦_
    infixl 101 _←_

    _←_ : ∀{d} → Term(d) → Term(d) → Term(d)
    _←_ a b = Apply a b

    _↦_ : (d : ℕ) → Term(𝐒(d)) → Term(d)
    _↦_ d expr = Abstract{d}(expr)

    [_] : ∀{d} → 𝕟(d) → Term(d)
    [_] n = Var n

  module LambdaSyntax where
    open OperSyntax using (_←_) renaming (_↦_ to 𝜆) public

    -- _⁡_ = _←_

{-
  substituteMap : ∀{d₁ d₂} → (𝕟(d₁) → Term(d₂)) → Term(d₁) → Term(d₂)
  substituteMap F (Apply(f)(x))    = Apply (substituteMap F (f)) (substituteMap F (x))
  substituteMap F (Var(v))         = F(v)
  substituteMap F (Abstract(body)) = Abstract (substituteMap F (body)) -- TODO: Probably incorrect
-}


  -- Substitutes the outer-most variable with a term in a term.
  -- Example:
  --   `substitute (val) (term)`
  --   means that all occurences of the outer-most variable is replaced with the term `val` in the term `term`.
  substitute : ∀{d} → Term(d) → Term(𝐒(d)) → Term(d)
  substitute       (val) (Apply(f)(x))    = Apply (substitute (val) (f)) (substitute (val) (x))
  substitute       (val) (Abstract(body)) = Abstract (substitute (depth-𝐒 val) (body))
  substitute       (val) (Var(𝟎))         = val
  substitute{𝐒(_)} (val) (Var(𝐒(v)))      = Var(v)

  -- β-reduction (beta).
  -- Reduces a term of form `f(x)` to `f[0 ≔ x]`.
  data _β⇴_ : ∀{a b} → Term(a) → Term(b) → Set₁ where
    intro : ∀{n}{f : Term(𝐒(𝐒(n)))}{x : Term(𝐒(n))} → (Apply(Abstract(f))(x) β⇴ substitute(x)(f))

  -- η-reduction (eta).
  -- Reduces a term of form `x ↦ f(x)` to `f`.
  data _η⇴_ : ∀{a b} → Term(a) → Term(b) → Set₁ where
    intro : ∀{n}{f : Term(𝐒(𝐒(n)))} → (Abstract(Apply(f)(Var(maximum))) η⇴ f)

  -- Reduction of expressions
  data _⇴_ : ∀{a b} → Term(a) → Term(b) → Set₁ where
    β-reduction : ∀{n}{f : Term(𝐒(𝐒(n)))}{x : Term(𝐒(n))} → (Apply(Abstract(f))(x) ⇴ substitute(x)(f))
    η-reduction : ∀{n}{f : Term(𝐒(𝐒(n)))} → (Abstract(Apply(f)(Var(maximum))) ⇴ f)

  module Combinators where
    open LambdaSyntax

    I = 𝜆 0 0
    K = 𝜆 0 (𝜆 1 0)
    S = 𝜆 0 (𝜆 1 (𝜆 2 ((0 ← 2) ← (1 ← 2))))
    B = 𝜆 0 (𝜆 1 (𝜆 2 (0 ← (1 ← 2))))
    C = 𝜆 0 (𝜆 1 (𝜆 2 ((0 ← 2) ← 1)))
    W = 𝜆 0 (𝜆 1 ((0 ← 1) ← 1))
    U = 𝜆 0 (0 ← 0)
    ω = U
    Ω = ω ← ω
    Y = 𝜆 0 ((𝜆 1 (0 ← (1 ← 1))) ← (𝜆 1 (0 ← (1 ← 1))))

    module Proofs where
      -- Y-self-reference : ∀{f} → (Star(_⇴_) (Y ← f) (f ← (Y ← f)))
      -- Y-self-reference = ?

  module Test where
    open OperSyntax

    test1Expr1 : Term(1)
    test1Expr1 = 1 ↦ (2 ↦ [ 2 ] ← [ 2 ]) ← [ 0 ] ← [ 1 ] ← [ 0 ]

    test1Expr2 : Term(2)
    test1Expr2 = 2 ↦ (3 ↦ [ 3 ] ← [ 3 ]) ← [ 1 ] ← [ 2 ] ← [ 1 ]

    test1Expr3 : Term(3)
    test1Expr3 = 3 ↦ (4 ↦ [ 4 ] ← [ 4 ]) ← [ 2 ] ← [ 3 ] ← [ 2 ]

    test1-1 : (var-𝐒 test1Expr1 ≡ test1Expr2)
    test1-1 = [≡]-intro

    test1-2 : (var-𝐒(var-𝐒 test1Expr1) ≡ test1Expr3)
    test1-2 = [≡]-intro

  {-
    test1-3 : (var-[+] 0 test1Expr1 ≡ test1Expr1)
    test1-3 = [≡]-intro

    test1-4 : (var-[+] 1 test1Expr1 ≡ test1Expr2)
    test1-4 = [≡]-intro

    test1-5 : (var-[+] 2 test1Expr1 ≡ test1Expr3)
    test1-5 = [≡]-intro

    test1Expr : Term(1)
    test1Expr = 1 ↦ (2 ↦ [ 2 ] ← [ 2 ]) ← [ 0 ] ← [ 1 ] ← [ 0 ]

    test1 : ((test1Expr) ≡ substituteOuter(0 ↦ [ 0 ])(0 ↦ test1Expr))
    test1 = [≡]-intro
  -}

-- This module assumes that the semantics is the following:
-- • Var(0) is the variable that was last/nearest/(most recently) bounded.
module IndexZeroNearest where
  open Transformations

  module LambdaSyntax where
    infix  100 𝜆_
    infixl 101 _←_

    _←_ : ∀{d} → Term(d) → Term(d) → Term(d)
    _←_ = Apply

    𝜆_ : ∀{d} → Term(𝐒(d)) → Term(d)
    𝜆_ = Abstract

  {-
  _==_ : ∀{d} → Term(d) → Term(d) → Bool
  Apply f x₁ == Apply g x₂ = {!(f == g) && (x₁ == x₂)!}
  Abstract f == Abstract g = f == g
  Var x == Var y = {!x == y!}
  _ == _ = 𝐹
  -}

  -- Substitutes a free variable with a term in a term, while also decrementing them.
  -- Example:
  --   `substitute-var var new term`
  --    is the term `term` but where the variable with the index `var` (counting starts from 0 on the outermost lambda binding) is replaced by `new`.
  substitute-var : ∀{d} → 𝕟(𝐒(d)) → Term(d) → Term(𝐒(d)) → Term(d)
  substitute-var var      new (Apply f x)     = Apply (substitute-var var new f) (substitute-var var new x)
  substitute-var var      new (Abstract body) = Abstract (substitute-var (𝐒(var)) (var-𝐒 new) body)
  substitute-var var      new (Var v) with ⋚-surjective {a = var} {b = v}
  substitute-var 𝟎        new (Var v)     | [∃]-intro ➕ ⦃ p ⦄ = [⊥]-elim(⋚-of-𝟎-not-+ {b = v})
  substitute-var (𝐒(var)) new (Var v)     | [∃]-intro ➕ ⦃ p ⦄ = Var {!!}
  substitute-var _        new (Var _)     | [∃]-intro 𝟎  ⦃ p ⦄ = new
  substitute-var _        new (Var (𝐒 v)) | [∃]-intro ➖ ⦃ p ⦄ = Var v
  {-
  substitute-var 𝟎        new (Var 𝟎)         = new
  substitute-var (𝐒(var)) new (Var 𝟎)         = Var 𝟎
  substitute-var 𝟎        new (Var(𝐒(v)))     = Var(v)
  substitute-var (𝐒(var)) new (Var(𝐒(v)))     = substitute-var (bound-𝐒 var)  new (Var(bound-𝐒 v))
-}

  -- TODO: Does not work as intended
  -- Substitutes the most recent free variable with a term in a term, while also decrementing them.
  -- Example:
  --   `substitute (val) (term)`
  --   means that all occurences of the outer-most variable is replaced with the term `val` in the term `term`.
  substitute-recent-var : ∀{d} → Term(d) → Term(𝐒(d)) → Term(d)
  substitute-recent-var        val (Apply(f)(x))    = Apply (substitute-recent-var val f) (substitute-recent-var val x)
  substitute-recent-var        val (Abstract(body)) = Abstract (substitute-recent-var (var-𝐒 val) body)
  substitute-recent-var        val (Var(𝟎))         = val
  substitute-recent-var {𝐒(_)} val (Var(𝐒(v)))      = Var v

  -- Substitutes all free variables by mapping all of them to new terms.
  substitute-vars : ∀{a b} → (𝕟(a) → Term(b)) → Term(a) → Term(b)
  substitute-vars        map (Apply(f)(x))    = Apply (substitute-vars map f) (substitute-vars map x)
  substitute-vars {a}{b} map (Abstract(body)) = Abstract (substitute-vars nextMap body) where
    -- A map function which preserves the newly introduced variable from the lambda abstraction.
    -- Specifically it maps the old ones (which are all variable index +1), and in the case where `map` introduces variables, it increments them too.
    nextMap : 𝕟(𝐒(a)) → Term(𝐒(b))
    nextMap(𝟎)    = Var(𝟎)
    nextMap(𝐒(n)) = var-𝐒(map n)
  substitute-vars        map (Var(n))         = map n

  -- β-reduction (beta).
  -- Reduces a term of form `f(x)` to `f[0 ≔ x]`.
  data _β⇴_ : ∀{a b} → Term(a) → Term(b) → Set₁ where
    intro : ∀{n}{f : Term(𝐒(𝐒(n)))}{x : Term(𝐒(n))} → (Apply(Abstract(f))(x) β⇴ substitute-recent-var(x)(f))

  -- η-reduction (eta).
  -- Reduces a term of form `x ↦ f(x)` to `f`.
  data _η⇴_ : ∀{a b} → Term(a) → Term(b) → Set₁ where
    intro : ∀{n}{f : Term(𝐒(𝐒(n)))} → (Abstract(Apply(f)(Var(𝟎))) η⇴ f)

  -- Reduction of expressions
  data _⇴_ : ∀{a b} → Term(a) → Term(b) → Set₁ where
    β-reduction : ∀{n}{f : Term(𝐒(𝐒(n)))}{x : Term(𝐒(n))} → (Apply(Abstract(f))(x) ⇴ substitute-recent-var(x)(f))
    η-reduction : ∀{n}{f : Term(𝐒(𝐒(n)))} → (Abstract(Apply(f)(Var(𝟎))) ⇴ f)

  module Functions where
    -- Identity function.
    -- Representation in function notation:
    --   x ↦ x
    --   0 ↦ 0
    id : Expression
    id = Abstract(Var(𝟎))

    -- Swap function.
    -- Intended as: f(x)(y) = (swap f)(y)(x)
    -- Representation in function notation:
    --   f ↦ x ↦ y ↦ (f(y))(x)
    --   0 ↦ 0
    swap : Expression
    swap =
      Abstract(
        Abstract(
          Abstract(
            (Apply
              (Apply
                (Var(𝐒(𝐒(𝟎))))
                (Var(𝟎))
              )
              (Var(𝐒(𝟎)))
            )
          )
        )
      )

    -- Function composition.
    -- Representation in function notation:
    --   f ↦ g ↦ x ↦ f(g(x))
    --   2 ↦ 1 ↦ 0 ↦ 2(1(0))
    _λ∘_ : Expression
    _λ∘_ =
      (Abstract
        (Abstract
          (Abstract
            (Apply
              (Var(𝐒(𝐒(𝟎))))
              (Apply
                (Var(𝐒(𝟎)))
                (Var(𝟎))
              )
            )
          )
        )
      )

    -- Applies a term on itself.
    -- Representation in function notation:
    --   f ↦ f(f)
    --   0 ↦ 0 0
    applySelf : Expression
    applySelf =
      (Abstract
        (Apply
          (Var(𝟎))
          (Var(𝟎))
        )
      )

    -- Fix point for reductions (Y-combinator).
    -- Satisfies: fix(f) ⇴ f(fix(f)) (TODO: Prove)
    -- Representation in function notation:
    --   f ↦ (g ↦ f(g g)) (g ↦ f(g g))
    --   1 ↦ (0 ↦ 1(0 0)) (0 ↦ 1(0 0))
    fix : Expression
    fix =
      (Abstract
        (Apply
          (Abstract
            (Apply
              (Var(𝐒(𝟎)))
              (Apply
                (Var(𝟎))
                (Var(𝟎))
              )
            )
          )

          (Abstract
            (Apply
              (Var(𝐒(𝟎)))
              (Apply
                (Var(𝟎))
                (Var(𝟎))
              )
            )
          )
        )
      )

    -- Natural numbers (Church numerals)
    -- Examples:
    --   • 0: f ↦ x ↦ x
    --   • 1: f ↦ x ↦ f(x)
    --   • 2: f ↦ x ↦ f(f(x))
    --   • 3: f ↦ x ↦ f(f(f(x)))
    module λℕ where
      -- Natural number constructor: Zero.
      -- Representation in function notation:
      --   f ↦ x ↦ x
      --   1 ↦ 0 ↦ 0
      λ𝟎 : Expression
      λ𝟎 =
        (Abstract
          (Abstract
            (Var(𝟎))
          )
        )

      -- Natural number constructor: Successor.
      -- Representation in function notation:
      --   n ↦ f ↦ x ↦ f(n(f(x)))
      --   2 ↦ 1 ↦ 0 ↦ 1(2(1(0)))
      λ𝐒 : Expression
      λ𝐒 =
        (Abstract
          (Abstract
            (Abstract
              (Apply
                (Var(𝐒(𝟎)))
                (Apply
                  (Var(𝐒(𝐒(𝟎))))
                  (Apply
                    (Var(𝐒(𝟎)))
                    (Var(𝟎))
                  )
                )
              )
            )
          )
        )

      -- Natural number constructor: Addition.
      -- Representation in function notation:
      --   a ↦ b ↦ f ↦ x ↦ (a(f))(b(f(x))) (TODO: Should it be ((b f)(x))?)
      --   3 ↦ 2 ↦ 1 ↦ 0 ↦ (3(1))(2(1(0)))
      _λ+_ : Expression
      _λ+_ =
        (Abstract
          (Abstract
            (Abstract
              (Abstract
                (Apply
                  (Apply
                    (Var(𝐒(𝐒(𝐒(𝟎)))))
                    (Var(𝐒(𝟎)))
                  )
                  (Apply
                    (Var(𝐒(𝐒(𝟎))))
                    (Apply
                      (Var(𝐒(𝟎)))
                      (Var(𝟎))
                    )
                  )
                )
              )
            )
          )
        )

      -- Natural number constructor: Multiplication.
      -- Representation in function notation:
      --   a ↦ b ↦ f ↦ a(b(f))

      -- Natural number constructor: Exponentiation.
      -- Representation in function notation:
      --   a ↦ b ↦ b(a)

  module ReductionProofs where
    open import Type.Dependent
    open import Logic.Propositional
    open import Logic.Predicate

    TermAny = Σ ℕ Term

    _⟶_ : TermAny → TermAny → Set₁
    _⟶_ a b = (Σ.right a) ⇴ (Σ.right b)

    open import ReductionSystem(_⟶_)

    -- Lambda calculus are confluent.
    -- Also called "Church-Rosser theorem".
    lambda-calculus-confluent : ∀{a} → Confluent(a)
    Σ.left  (∃.witness (lambda-calculus-confluent ab ac)) = {!!}
    Σ.right (∃.witness (lambda-calculus-confluent ab ac)) = {!!}
    ∃.proof (lambda-calculus-confluent ab ac) = [∧]-intro {!!} {!!}

  module Test where
    open Transformations
    open LambdaSyntax

    test1 : Term(1)
    test1 = (𝜆 (1 ← 0)) ← 0

    test2 : Term(0)
    test2 = (𝜆 ((𝜆 0) ← 0)) ← (𝜆 0)
{-
    test1-test2-subst1 : substitute-vars (\_ -> (𝜆 (0 ← 3)) ← 2) test1 ≡ test2
    test1-test2-subst1 = {!!} --[≡]-intro

    test1-test2-subst2 : substitute-recent-var ((𝜆 (0 ← 3)) ← 2) test1 ≡ test2
    test1-test2-subst2 = {!!} -- [≡]-intro
-}

    test3 : Term(1)
    test3 = 0 ← (𝜆 (0 ← (𝜆 0)))
--    test3 = 0 ← (𝜆 (1 ← (𝜆 2)))

    test4 : Term(0)
    test4 = (𝜆 0) ← (𝜆 ((𝜆 0) ← (𝜆 (𝜆 0))))
--          (𝜆 0) ← (𝜆 (0 ← (𝜆 1)))

    test3-test4-subst2 : substitute-recent-var (𝜆 0) test3 ≡ test4
    test3-test4-subst2 = {!!} -- [≡]-intro

-- COmputation rules:
-- (e ⟶ e') → (λ x e → λ x e') partial evaluation
-- (e₀ ⟶ e₀') → (e₀ e₁ ⟶ e₀' e₁)
-- (e₁ ⟶ e₁') → (e₀ e₁ ⟶ e₀ e₁')
-- Computation rule is confluent.
-- (∀e∃e'. Normal(e') ∧ (e ⟶* e')) is undecidable. Example: e = δ δ and e = I I where I = λ x x and δ = λx (x x). This was historically the first known undecidable problem?

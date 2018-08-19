module Logic.LambdaCalculus where

import      Lvl
open import Data.Boolean
open import Numeral.Natural
open import Numeral.Natural.Oper.Comparisons
open import Numeral.FiniteStrict
  renaming (𝟎 to 𝟎ᶠ ; 𝐒 to 𝐒ᶠ)
open import Numeral.Natural.Function
open import Numeral.Natural.Oper

-- TODO: Someone else did something similiar apparently: https://gist.github.com/gallais/303cfcfe053fbc63eb61
-- TODO: Execution is possible, but limited? https://stackoverflow.com/questions/2583337/strictly-positive-in-agda#

-- A lambda term (A term in the language of lambda calculus).
-- This is encoded with an abstraction depth which ensures that every term is well-formed.
data Term : ℕ → Set where
  -- The term which represents applying the second term on the first term.
  -- Representation in function notation:
  --   (Apply f(x)) is f(x)
  Apply    : ∀{d} → Term(d) → Term(d) → Term(d)

  -- The term which represents bounding a new variable (introducing a variable).
  -- Representation in function notation:
  --   (Abstract{n} term) is (xₙ ↦ term)
  Abstract : ∀{d} → Term(𝐒(d)) → Term(d)

  -- The term which represents a specific variable in scope.
  -- Representation in function notation:
  --   (Var(n)) is xₙ
  Var      : ∀{d} → 𝕟(d) → Term(d)

Expression : Set
Expression = Term(0)

module Functions where
  -- Identity function.
  -- Representation in function notation:
  --   x ↦ x
  --   0 ↦ 0
  id : Expression
  id = Abstract(Var(𝟎ᶠ))

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
            (Var(𝐒ᶠ(𝐒ᶠ(𝟎ᶠ))))
            (Apply
              (Var(𝐒ᶠ(𝟎ᶠ)))
              (Var(𝟎ᶠ))
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
          (Var(𝟎ᶠ))
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
              (Var(𝐒ᶠ(𝟎ᶠ)))
              (Apply
                (Var(𝐒ᶠ(𝐒ᶠ(𝟎ᶠ))))
                (Apply
                  (Var(𝐒ᶠ(𝟎ᶠ)))
                  (Var(𝟎ᶠ))
                )
              )
            )
          )
        )
      )

    -- Natural number constructor: Addition.
    -- Representation in function notation:
    --   a ↦ b ↦ f ↦ x ↦ (a(f))(b(f(x)))
    --   3 ↦ 2 ↦ 1 ↦ 0 ↦ (3(1))(2(1(0)))
    _λ+_ : Expression
    _λ+_ =
      (Abstract
        (Abstract
          (Abstract
            (Abstract
              (Apply
                (Apply
                  (Var(𝐒ᶠ(𝐒ᶠ(𝐒ᶠ(𝟎ᶠ)))))
                  (Var(𝐒ᶠ(𝟎ᶠ)))
                )
                (Apply
                  (Var(𝐒ᶠ(𝐒ᶠ(𝟎ᶠ))))
                  (Apply
                    (Var(𝐒ᶠ(𝟎ᶠ)))
                    (Var(𝟎ᶠ))
                  )
                )
              )
            )
          )
        )
      )

module Transformations where
  open import Numeral.FiniteStrict.Bound{Lvl.𝟎}
  open import Numeral.Natural.Oper.Properties{Lvl.𝟎}
  open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
  open import Relator.Equals.Proofs{Lvl.𝟎}{Lvl.𝟎}

  -- Increment the depth level of the given term
  depth-𝐒 : ∀{d} → Term(d) → Term(𝐒(d))
  depth-𝐒 (Apply(f)(x)) = Apply (depth-𝐒(f)) (depth-𝐒(x))
  depth-𝐒 (Abstract(body))    = Abstract(depth-𝐒(body))
  depth-𝐒 (Var(n))            = Var(bound-𝐒 (n))

  -- Add to the depth level of the given term
  depth-[+] : ∀{d₁ d₂} → Term(d₁) → Term(d₁ + d₂)
  depth-[+] {d₁}{d₂} (Apply(f)(x)) = Apply (depth-[+] {d₁}{d₂} (f)) (depth-[+] {d₁}{d₂} (x))
  depth-[+] {d₁}{d₂} (Abstract(body)) =
    (Abstract
      ([≡]-elimᵣ
        ([+1]-commutativity {d₁}{d₂})
        {Term}
        (depth-[+] {𝐒(d₁)}{d₂} (body))
      )
    )
  depth-[+] {d₁}{d₂} (Var(n)) = Var(bound-[+] {d₁}{d₂} (n))

  -- TODO: depth-max

  Apply₊ : ∀{d₁ d₂} → Term(d₁ + d₂) → Term(d₁) → Term(d₁ + d₂)
  Apply₊ {d₁}{d₂} f(x) = Apply f(depth-[+] {d₁}{d₂} (x))

  module IndexOrder1 where -- TODO: Rename
    -- Substitutes a variable with a term.
    -- This substitution assumes that the semantics is the following:
    --   • Var(0) is the variable that was first/furthest/(least recently) bounded.
    -- Example:
    --   `substitute (var) (val) (term)`
    --   means that all occurences of the variable `var` is replaced with the term `val` in the term `term`.
    -- TODO: Should decrement one depth level
    {-substitute : ∀{d} → 𝕟(𝐒(d)) → Term(d) → Term(𝐒(d)) → Term(d)
    substitute       (var) (val) (Apply(f)(x)) = Apply (substitute (var) (val) (f)) (substitute (var) (val) (x))
    substitute{𝐒(_)} (var) (val) (Var(n)) =
      if([𝕟]-to-[ℕ] (var) ≡? [𝕟]-to-[ℕ] (n)) then
        (val)
      else
        (Var(n))
    substitute       (var) (val) (Abstract(body)) = Abstract (substitute (bound-𝐒(var)) (depth-𝐒 val) (body))
    -}
    -- TODO: This is incorrect. It just replaces all occurrences of Var(n), which is incorrect in any index order
    substitute : ∀{d} → 𝕟(d) → Term(d) → Term(d) → Term(d)
    substitute       (var) (val) (Apply(f)(x)) = Apply (substitute (var) (val) (f)) (substitute (var) (val) (x))
    substitute{𝟎}    (var) (val) (Var())
    substitute{𝐒(_)} (var) (val) (Var(n)) =
      if([𝕟]-to-[ℕ] (var) ≡? [𝕟]-to-[ℕ] (n)) then
        (val)
      else
        (Var(n))
    substitute       (var) (val) (Abstract(body)) = Abstract (substitute (bound-𝐒(var)) (depth-𝐒 val) (body))


  module IndexOrder2 where
  {-
    -- Substitutes a variable with a term.
    -- This substitution assumes that the semantics is the following:
    --   • Var(0) is the variable that was last/nearest/(most recently) bounded.
    -- Example:
    --   `substitute (var) (val) (term)`
    --   means that all occurences of the variable `var` is replaced with the term `val` in the term `term`.
    substitute : ∀{d₁ d₂} → 𝕟(𝐒(d₁)) → Term(𝐒(d₁)) → Term(𝐒(d₁) + d₂) → Term(d₁ + d₂)
    substitute       (𝐒ᶠ(var)) (val) (Apply(f)(x)) = Apply (substitute (var) (val) (f)) (substitute (var) (val) (x))
    substitute{𝟎}    (var)    (val) (Var())
    substitute{𝐒(_)} (var)    (val) (Var(n)) =
      if([𝕟]-to-[ℕ] (var) ≡? [𝕟]-to-[ℕ] (n)) then
        (val)
      else
        (Var(n))
    substitute       (𝐒ᶠ(var)) (val) (Abstract(body)) = Abstract (substitute (bound-𝐒(var)) (depth-𝐒 val) (body))

    -- Reducible (Reduction relation)
    -- TODO: Would this definition suffice? Though, [⇴]-with makes it much more difficult to define a normal form. One could put F ≔ const(_), and then (x ⇴ x).
    data _⇴_ : ∀{a b} → Term(𝐒(a)) → Term(𝐒(b)) → Set₁ where
      -- Reduces f(x) to f[0 ≔ x]
      β-reduction : ∀{n}{f : Term(𝐒(𝐒(n)))}{x : Term(𝐒(n))} → (Apply(Abstract(f))(x) ⇴ substitute(𝟎ᶠ)(depth-𝐒(x))(f)) -- TODO: x should not increase depth level
      η-reduction : ∀{n}{f : Term(𝐒(𝐒(n)))} → (Abstract(Apply(f)(Var(𝟎ᶠ))) ⇴ f)
      [⇴]-with    : ∀{n₁ n₂}{A : Term(𝐒(n₁))}{B : Term(𝐒(n₁))} → (A ⇴ B) → ∀{F : Term(𝐒(n₁)) → Term(𝐒(n₂))} → (F(A) ⇴ F(B))
  -}

  {- TODO: What is this good for?
  β-reduce : ∀{d₁ d₂} → 𝕟(d₁ + 𝐒(d₂)) → Term(d₁ + 𝐒(d₂)) → Term(𝐒(d₂)) → Term(d₂)
  β-reduce{d₁}   {d₂}    (var) (val) (Apply(f)(x))    = Apply{d₂} (β-reduce{d₁}{d₂} (var)(val) (f)) (β-reduce (var)(val) (x))
  β-reduce{d₁}   {d₂}    (var) (val) (Abstract(body)) = Abstract (β-reduce{d₁}{𝐒(d₂)} (bound-𝐒 var)(val) (body))
  β-reduce{𝟎}    {𝐒(d₂)} (𝟎ᶠ)      (val) (Var(n)) = Var{d₂}(𝟎ᶠ)
  β-reduce{𝟎}    {𝐒(d₂)} (𝐒ᶠ(var)) (val) (Var(n)) = Var{d₂}(var)
  β-reduce{𝐒(d₁)}{𝐒(d₂)} (var)     (val) (Var(n)) = Var{d₂}(n)
    if([𝕟]-to-[ℕ](var) ≡? [𝕟]-to-[ℕ](n)) then
      (val)
    else
      (val) -- (Var{max (𝐒 d₁) (𝐒 d₂)} (bound-maxᵣ n))
  -}

module Test where
  open        Transformations
  open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
  open import Relator.Equals.Proofs{Lvl.𝟎}{Lvl.𝟎}

  test1 : Expression
  test1 = Abstract(Abstract(Apply (Var(𝐒ᶠ(𝟎ᶠ))) (Var(𝟎ᶠ))))
  -- test1 = Abstract{0}(Abstract{1}(Apply{2} (Var{1}(𝟎ᶠ)) (Var{1}(𝐒ᶠ(𝟎ᶠ)))))
  -- f ↦ x ↦ f(x)
  -- λλ. 1 0

  test2 : Expression
  test2 = Abstract(Abstract(Apply (Var(𝐒ᶠ(𝟎ᶠ))) (Var(𝐒ᶠ(𝟎ᶠ)))))
  -- f ↦ x ↦ f(f)
  -- λλ. 1 1

  test3 : Expression
  test3 = Abstract(Abstract(Apply (Var(𝟎ᶠ)) (Var(𝟎ᶠ))))
  -- f ↦ x ↦ x(x)
  -- λλ. 0 0

  -- test4 : Expression
  -- test4 = Var(𝟎ᶠ)

  -- test5 : Expression
  -- test5 = Abstract(Abstract(Apply (Var(𝐒ᶠ(𝟎ᶠ))) (Var(𝐒ᶠ(𝐒ᶠ(𝟎ᶠ))))))

  test6 : Expression
  test6 =
    Abstract
      (Apply
        (Apply
          (Abstract(Apply (Var(𝟎ᶠ)) (Var(𝐒ᶠ(𝟎ᶠ)))))
          (Abstract(Apply (Var(𝟎ᶠ)) (Var(𝐒ᶠ(𝟎ᶠ)))))
        )
        (Var(𝟎ᶠ))
      )
  -- x ↦ ((f ↦ f(x)) (g ↦ g(x))) (x)
  -- λ. ((λ. 0 1) (λ. 0 1)) 0

  test7 : Expression
  test7 = Abstract(Abstract(Apply (Var(𝐒ᶠ(𝟎ᶠ))) (depth-𝐒(depth-𝐒(Functions.id)))))

  -- test1-subst : substitute (𝐒ᶠ(𝟎ᶠ)) (Var(𝟎ᶠ)) (depth-𝐒(test1)) ≡ Abstract(Abstract(Apply (Var(𝟎ᶠ)) (Var(𝟎ᶠ))))
  -- test1-subst = [≡]-intro

  -- test2-subst : substitute(𝐒ᶠ(𝟎ᶠ)) (depth-𝐒(Functions.id)) (depth-𝐒(test1)) ≡ Abstract(Abstract(Apply (Functions.id) (Var(𝟎ᶠ))))
  -- test2-subst = [≡]-intro

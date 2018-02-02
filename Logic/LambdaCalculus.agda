module Logic.LambdaCalculus where

import      Lvl
open import Boolean
open import Numeral.Natural
open import Numeral.Natural.BooleanOper
open import Numeral.Finite
  renaming (𝟎fin to 𝟎ᶠ ; 𝐒fin to 𝐒ᶠ)
open import Numeral.Natural.Function
open import Numeral.Natural.Oper

-- A lambda term (A term in the language of lambda calculus).
-- This is encoded with an abstraction depth which ensures that every term is well-formed.
data Term : ℕ → Set where
  Application : ∀{d} → Term(d) → Term(d) → Term(d)
  Abstract    : ∀{d} → Term(𝐒(d)) → Term(d)
  Var         : ∀{d} → ℕfin(d) → Term(𝐒(d))

Expression : Set
Expression = Term(0)

module Functions where
  id : Expression
  id = Abstract(Var(𝟎ᶠ))

  Church-𝟎 : Expression
  Church-𝟎 =
    (Abstract
      (Abstract
        (Var(𝟎ᶠ))
      )
    )

  Church-𝐒 : Expression
  Church-𝐒 =
    (Abstract
      (Abstract
        (Abstract
          (Application
            (Var(𝐒ᶠ(𝟎ᶠ)))
            (Application
              (Var(𝐒ᶠ(𝐒ᶠ(𝟎ᶠ))))
              (Application
                (Var(𝐒ᶠ(𝟎ᶠ)))
                (Var(𝟎ᶠ))
              )
            )
          )
        )
      )
    )

module Transformations where
  open        Numeral.Finite.Theorems{Lvl.𝟎}
  open import Numeral.Natural.Oper.Properties{Lvl.𝟎}
  open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
  open import Relator.Equals.Theorems{Lvl.𝟎}{Lvl.𝟎}

  -- Increment the depth level of the given term
  depth-𝐒 : ∀{d} → Term(d) → Term(𝐒(d))
  depth-𝐒 (Application(f)(x)) = Application (depth-𝐒(f)) (depth-𝐒(x))
  depth-𝐒 (Abstract(body))    = Abstract(depth-𝐒(body))
  depth-𝐒 (Var(n))            = Var(upscale-𝐒 (n))

  -- Add to the depth level of the given term
  depth-[+] : ∀{d₁ d₂} → Term(d₁) → Term(d₁ + d₂)
  depth-[+] {d₁}{d₂} (Application(f)(x)) = Application (depth-[+] {d₁}{d₂} (f)) (depth-[+] {d₁}{d₂} (x))
  depth-[+] {d₁}{d₂} (Abstract(body)) =
    (Abstract
      ([≡]-elimᵣ
        ([+1]-commutativity {d₁}{d₂})
        {Term}
        (depth-[+] {𝐒(d₁)}{d₂} (body))
      )
    )
  depth-[+] {𝐒(d₁)}{d₂} (Var(n)) =
    ([≡]-elimₗ
      ([+1]-commutativity {d₁}{d₂})
      {Term}
      (Var(upscale-[+] {d₁}{d₂} (n)))
    )

  -- TODO
  -- Apply : ∀{d₂ d₁} → Term(d₁ + d₂) → Term(d₁) → Term(d₁ + d₂)
  -- Apply {d₁}{d₂} (f)(x) = Application(f)(depth-[+] {d₁}{d₂} (x))

  substitute : ∀{d} → ℕfin(d) → Term(d) → Term(d) → Term(d)
  substitute (var) (val) (Application(f)(x)) = Application (substitute (var) (val) (f)) (substitute (var) (val) (x))
  substitute (var) (val) (Var(n)) =
    if([ℕfin]-to-[ℕ] (var) ≡? [ℕfin]-to-[ℕ] (n)) then
      (val)
    else
      (Var(n))
  substitute (var) (val) (Abstract(body)) = Abstract (substitute (upscale-𝐒(var)) (depth-𝐒 val) (body))

  {-
  β-reduce : ∀{d₁ d₂} → ℕfin(d₁ + 𝐒(d₂)) → Term(d₁ + 𝐒(d₂)) → Term(𝐒(d₂)) → Term(d₂)
  β-reduce{d₁}   {d₂}    (var) (val) (Application(f)(x))    = Application{d₂} (β-reduce{d₁}{d₂} (var)(val) (f)) (β-reduce (var)(val) (x))
  β-reduce{d₁}   {d₂}    (var) (val) (Abstract(body)) = Abstract (β-reduce{d₁}{𝐒(d₂)} (upscale-𝐒 var)(val) (body))
  β-reduce{𝟎}    {𝐒(d₂)} (𝟎ᶠ)      (val) (Var(n)) = Var{d₂}(𝟎ᶠ)
  β-reduce{𝟎}    {𝐒(d₂)} (𝐒ᶠ(var)) (val) (Var(n)) = Var{d₂}(var)
  β-reduce{𝐒(d₁)}{𝐒(d₂)} (var)     (val) (Var(n)) = Var{d₂}(n)
    if([ℕfin]-to-[ℕ](var) ≡? [ℕfin]-to-[ℕ](n)) then
      (val)
    else
      (val) -- (Var{max (𝐒 d₁) (𝐒 d₂)} (upscale-maxᵣ n))
  -}

-- Reducible (Reduction relation)
-- data _⇴_ : Term → Term → Set where
--   β-reduction : (val : ∀{d} → Term(d)) → ∀{φ} → (Abstract(φ) ⇴ β-reduce(0)(val)(φ))

module Test where
  open        Transformations
  open import Relator.Equals{Lvl.𝟎}{Lvl.𝟎}
  open import Relator.Equals.Theorems{Lvl.𝟎}{Lvl.𝟎}

  test1 : Expression
  test1 = Abstract(Abstract(Application (Var(𝐒ᶠ(𝟎ᶠ))) (Var(𝟎ᶠ))))
  -- test1 = Abstract{0}(Abstract{1}(Application{2} (Var{1}(𝟎ᶠ)) (Var{1}(𝐒ᶠ(𝟎ᶠ)))))
  -- f ↦ x ↦ f(x)
  -- λλ. 1 0

  test2 : Expression
  test2 = Abstract(Abstract(Application (Var(𝐒ᶠ(𝟎ᶠ))) (Var(𝐒ᶠ(𝟎ᶠ)))))
  -- f ↦ x ↦ f(f)
  -- λλ. 1 1

  test3 : Expression
  test3 = Abstract(Abstract(Application (Var(𝟎ᶠ)) (Var(𝟎ᶠ))))
  -- f ↦ x ↦ x(x)
  -- λλ. 0 0

  -- test4 : Expression
  -- test4 = Var(𝟎ᶠ)

  -- test5 : Expression
  -- test5 = Abstract(Abstract(Application (Var(𝐒ᶠ(𝟎ᶠ))) (Var(𝐒ᶠ(𝐒ᶠ(𝟎ᶠ))))))

  test6 : Expression
  test6 =
    Abstract
      (Application
        (Application
          (Abstract(Application (Var(𝟎ᶠ)) (Var(𝐒ᶠ(𝟎ᶠ)))))
          (Abstract(Application (Var(𝟎ᶠ)) (Var(𝐒ᶠ(𝟎ᶠ)))))
        )
        (Var(𝟎ᶠ))
      )
  -- x ↦ ((f ↦ f(x)) (g ↦ g(x))) (x)
  -- λ. ((λ. 0 1) (λ. 0 1)) 0

  test7 : Expression
  test7 = Abstract(Abstract(Application (Var(𝐒ᶠ(𝟎ᶠ))) (depth-𝐒(depth-𝐒(Functions.id)))))

  test1-subst : substitute (𝐒ᶠ(𝟎ᶠ)) (Var(𝟎ᶠ)) (depth-𝐒(test1)) ≡ Abstract(Abstract(Application (Var(𝟎ᶠ)) (Var(𝟎ᶠ))))
  test1-subst = [≡]-intro

  -- test2-subst : substitute(𝐒ᶠ(𝟎ᶠ)) (depth-𝐒(Functions.id)) (depth-𝐒(test1)) ≡ Abstract(Abstract(Application (Functions.id) (Var(𝟎ᶠ))))
  -- test2-subst = [≡]-intro

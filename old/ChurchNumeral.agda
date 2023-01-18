-- Natural numbers using the "Church numerals"-representation.
-- Note: This module needs the `cong-abstract` reduction rule to work.
module Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.ChurchNumeral where

import      Lvl
open import Data
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.Syntax.ExplicitLambda
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators using (K ; 𝈲)
open import Logic.Predicate
open import Numeral.Natural as ℕ using (ℕ)
open import Syntax.Function
open import Syntax.Number
open import Type

𝟎 = 𝈲                                 -- Zero (constructor)
𝐒 = 𝜆 0 (𝜆 1 (𝜆 2 (1 ← (0 ← 1 ← 2)))) -- Successor (constructor)

Add = 𝜆 0 (𝜆 1 (𝜆 2 (𝜆 3 (0 ← 2 ← (1 ← 2 ← 3)))))
Mul = 𝜆 0 (𝜆 1 (𝜆 2 (0 ← (1 ← 2))))
Exp = 𝜆 0 (𝜆 1 (1 ← 0))

ApplyIterated : ∀{d} → Term(d) → Term(d) → ℕ → Term(d)
ApplyIterated f x ℕ.𝟎      = x
ApplyIterated f x (ℕ.𝐒(n)) = f ← ApplyIterated f x n

ℕrepr₂ = ApplyIterated{2} 0 1
ℕrepr = \n → 𝜆 0 (𝜆 1 (ℕrepr₂ n))

module Proofs where
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction.Proofs
  open import Formalization.LambdaCalculus.ByVarCount.Functions renaming (varShift𝐒₀ to _↑ ; varShift𝐒Outermost to _↑')
  open import Formalization.LambdaCalculus.ByVarCount.Functions.Proofs
  open        Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators.Proofs using (K-reduction ; 𝈲-reduction)
  open import Functional using (swap)
  open import Numeral.Finite as 𝕟 using (𝕟)
  open import Numeral.Natural as ℕ using (ℕ)
  open import Numeral.Natural.Oper
  open import Numeral.Natural.Oper.Proofs
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv
  open import Relator.ReflexiveTransitiveClosure
  open import Relator.ReflexiveTransitiveClosure.Proofs
  open import Structure.Function
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  private variable n n₁ n₂ : ℕ
  private variable i : 𝕟(n)
  private variable f g h t x y z : Term(n)

  {-
  open import Function.Iteration
  open import Numeral.Finite as 𝕟 using (𝕟₌)
  import      Numeral.Finite.Bound as 𝕟
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Evaluator

  test-sub1 : let x = (𝜆 1 (1 ← 0)) in
    substituteVar 0 x (𝜆 2 (1 ← (0 ← 1 ← 2) ← (𝜆 3 (3 ← 2 ← 1 ← 0)) ← (𝜆 3 (3 ← (𝜆 4 (2 ← 0 ← 3)) ← 1 ← 0))))
    ≡ (𝜆 1 (0 ← ((x ↑) ← 0 ← 1) ← (𝜆 2 (2 ← 1 ← 0 ← (x ↑ ↑))) ← (𝜆 2 (2 ← (𝜆 3 (1 ← (x ↑ ↑ ↑) ← 2)) ← 0 ← (x ↑ ↑)))))
  test-sub1 = [≡]-intro

  test-sub2 : let x = (𝜆 1 (1 ← 0)) ← 0 in
    substituteVar 1 x (𝜆 2 (1 ← (0 ← 1 ← 2) ← (𝜆 3 (3 ← 2 ← 1 ← 0)) ← (𝜆 3 (3 ← (𝜆 4 (2 ← 0 ← 3)) ← 1 ← 0))))
    ≡ (𝜆 1 ((x ↑') ← (0 ← (x ↑') ← 1) ← (𝜆 2 (2 ← 1 ← (x ↑' ↑') ← 0)) ← (𝜆 2 (2 ← (𝜆 3 (1 ← 0 ← 2)) ← (x ↑' ↑') ← 0))))
  test-sub2 = [≡]-intro

  test4 = {!normalize applicativeOrder ((𝜆 2 (𝜆 3 (2 ← 3))) ← 0)!}
  test5 = {!normalize applicativeOrder ((𝜆 1 (𝜆 2 (1 ← 2))) ← 0)!}
  test2 = {!normalize applicativeOrder (Mul ← ℕrepr 2 ← ℕrepr 2)!}
  test3 = {!normalize applicativeOrder (Add ← ℕrepr 2 ← ℕrepr 4)!}
  test1 = {!normalize applicativeOrder (𝐒 ← ℕrepr 2)!}
  test0 = {!normalize applicativeOrder ((ℕrepr(10) ↑ ↑) ← 0 ← 1)!}
  test6 = {!normalize applicativeOrder (ℕrepr₂(10))!}

  -- λ0 (λ1 (1 ← ((0 ← 1) ← (λ2 (λ3 3)))))
  -}

  Nat : Expression → Type
  Nat e = ∃(n ↦ e ⇴* ℕrepr(n))

  substituteVar-on-ApplyIterated : substituteVar i t (ApplyIterated f x n) ≡ ApplyIterated (substituteVar i t f) (substituteVar i t x) n
  substituteVar-on-ApplyIterated {n = ℕ.𝟎} = [≡]-intro
  substituteVar-on-ApplyIterated {i = i}{t = t}{f = f}{x = x}{n = ℕ.𝐒 n}
    rewrite substituteVar-on-ApplyIterated {i = i}{t = t}{f = f}{x = x}{n = n}
    = [≡]-intro
  {-# REWRITE substituteVar-on-ApplyIterated #-}

  varShift𝐒-on-ApplyIterated : varShift𝐒 i (ApplyIterated f x n) ≡ ApplyIterated (varShift𝐒 i f) (varShift𝐒 i x) n
  varShift𝐒-on-ApplyIterated {n = ℕ.𝟎} = [≡]-intro
  varShift𝐒-on-ApplyIterated {i = i}{f = f}{x = x}{n = ℕ.𝐒 n}
    rewrite varShift𝐒-on-ApplyIterated {i = i}{f = f}{x = x}{n = n}
    = [≡]-intro
  {-# REWRITE varShift𝐒-on-ApplyIterated #-}

  ApplyIterated-[+] : ApplyIterated f (ApplyIterated f x n₁) n₂ ≡ ApplyIterated f x (n₁ + n₂)
  ApplyIterated-[+] {n₂ = ℕ.𝟎} = [≡]-intro
  ApplyIterated-[+] {f = f}{x = x}{n₁ = n₁}{n₂ = ℕ.𝐒 n₂}
    rewrite ApplyIterated-[+] {f = f}{x = x}{n₁ = n₁}{n₂ = n₂}
    = [≡]-intro

  ApplyIterated-[⋅] : ApplyIterated(𝜆 n (ApplyIterated(varShift𝐒 i f) (Var 𝕟.maximum) n₂)) x n₁ ⇴* ApplyIterated{n} f x (n₁ ⋅ n₂)
  ApplyIterated-[⋅] {n₁ = ℕ.𝟎} = reflexivity(_⇴*_)
  ApplyIterated-[⋅] {n = n}{i = i}{f = f}{n₂ = n₂}{x = x}{n₁ = ℕ.𝐒 n₁} =
    ApplyIterated(𝜆 n (ApplyIterated (varShift𝐒 i f) (Var 𝕟.maximum) n₂)) x (ℕ.𝐒(n₁))                                           🝖[ _⇴*_ ]-[]
    (𝜆 n (ApplyIterated (varShift𝐒 i f) (Var 𝕟.maximum) n₂)) ← ApplyIterated(𝜆 n (ApplyIterated (varShift𝐒 i f) (Var 𝕟.maximum) n₂)) x n₁ 🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Apply _) (ApplyIterated-[⋅] {n = n}{f = f}{n₂ = n₂}{x = x}{n₁ = n₁}) ]
    (𝜆 n (ApplyIterated (varShift𝐒 i f) (Var 𝕟.maximum) n₂)) ← ApplyIterated{n} f x (n₁ ⋅ n₂)                                   🝖[ _⇴_ ]-[ {!β!} ]-sub
    ApplyIterated f (ApplyIterated{n} f x (n₁ ⋅ n₂)) n₂                                                                         🝖[ _⇴*_ ]-[ sub₂(_≡_)(_⇴*_) (ApplyIterated-[+] {f = f}{x = x}{n₁ = n₁ ⋅ n₂}{n₂ = n₂}) ]
    (ApplyIterated{n} f x ((n₁ ⋅ n₂) + n₂))                                                                                     🝖[ _⇴*_ ]-[ sub₂(_≡_)(_⇴*_) (symmetry(_≡_) (congruence₁(ApplyIterated f x) ([⋅]-with-[𝐒]ₗ {x = n₁}{y = n₂}))) ]
    ApplyIterated f x (ℕ.𝐒(n₁) ⋅ n₂) 🝖-end

  ℕrepr-application-to-ApplyIterated : (ℕrepr(n) ← x ← y) ⇴* ApplyIterated x y n
  ℕrepr-application-to-ApplyIterated {n = n}{x = x}{y = y} =
    ℕrepr(n) ← x ← y                          🝖[ _⇴*_ ]-[]
    (𝜆 0 (𝜆 1 (ApplyIterated 0 1 n))) ← x ← y 🝖[ _⇴_ ]-[ cong-applyₗ β ]-sub
    -- {!!}       🝖[ _⇴*_ ]-[ {!compatible₁(_⇴*_)(_⇴*_)(Apply _) (sub₂(_≡_)(_⇴*_) (substituteVar-on-ApplyIterated{n = n}))!} ]
    (𝜆 0 (ApplyIterated (x ↑) 0 n)) ← y       🝖[ _⇴_ ]-[ β ]-sub
    -- _                                         🝖[ _⇴*_ ]-[ {!!}  ] -- sub₂(_≡_)(_⇴*_) (substituteVar-on-ApplyIterated{n = n})
    ApplyIterated x y n                       🝖-end

  -- TODO: Same proof as ℕrepr-application-to-ApplyIterated
  ℕrepr-application-identity : ((ℕrepr(n) ↑ ↑) ← 0 ← 1) ⇴* ℕrepr₂(n)
  ℕrepr-application-identity {n = n} =
    (ℕrepr(n) ↑ ↑) ← 0 ← 1                    🝖[ _⇴*_ ]-[]
    {!!}       🝖[ _⇴_ ]-[ {!!} ]-sub
    (𝜆 2 (𝜆 3 (ApplyIterated 2 3 n))) ← 0 ← 1 🝖[ _⇴_ ]-[ cong-applyₗ β ]-sub
    {!!}       🝖[ _⇴_ ]-[ {!!} ]-sub
    (𝜆 2 (ApplyIterated 0 2 n)) ← 1           🝖[ _⇴_ ]-[ β ]-sub
    {!!}       🝖[ _⇴_ ]-[ {!!} ]-sub
    ApplyIterated 0 1 n                       🝖[ _⇴*_ ]-[]
    ℕrepr₂(n)                                 🝖-end

  𝐒-is-nat : Nat x → Nat(𝐒 ← x)
  𝐒-is-nat {x = x} ([∃]-intro n ⦃ p ⦄) =
    ([∃]-intro (ℕ.𝐒(n)) ⦃
      𝐒 ← x                                               🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Apply _) p ]
      𝐒 ← ℕrepr(n)                                        🝖[ _⇴_ ]-[ β ]-sub
      𝜆 0 (𝜆 1 (0 ← ((ℕrepr(n) ↑ ↑) ← 0 ← 1)))            🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Abstract) (compatible₁(_⇴*_)(_⇴*_)(Abstract) (compatible₁(_⇴*_)(_⇴*_)(Apply _) ℕrepr-application-identity)) ]
      𝜆 0 (𝜆 1 (0 ← ℕrepr₂ n))                            🝖[ _⇴*_ ]-[]
      𝜆 0 (𝜆 1 (ℕrepr₂(ℕ.𝐒(n))))                          🝖[ _⇴*_ ]-[]
      ℕrepr(ℕ.𝐒(n)) 🝖-end
    ⦄)

  Add-is-nat : Nat x → Nat y → Nat(Add ← x ← y)
  Add-is-nat {x = x}{y = y} ([∃]-intro X ⦃ px ⦄) ([∃]-intro Y ⦃ py ⦄) =
    ([∃]-intro (Y + X) ⦃
      Add ← x ← y                                                       🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Apply _) py ]
      Add ← x ← ℕrepr(Y)                                                🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(swap Apply _) (compatible₁(_⇴*_)(_⇴*_)(Apply _) px) ]
      Add ← ℕrepr(X) ← ℕrepr(Y)                                         🝖[ _⇴_ ]-[ cong-applyₗ β ]-sub
      (𝜆 0 (𝜆 1 (𝜆 2 ((ℕrepr(X) ↑ ↑ ↑) ← 1 ← (0 ← 1 ← 2))))) ← ℕrepr(Y) 🝖[ _⇴_ ]-[ β ]-sub
      𝜆 0 (𝜆 1 ((ℕrepr(X) ↑ ↑) ← 0 ← ((ℕrepr(Y) ↑ ↑) ← 0 ← 1)))         🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Abstract) (compatible₁(_⇴*_)(_⇴*_)(Abstract) (
        (ℕrepr(X) ↑ ↑) ← 0 ← ((ℕrepr(Y) ↑ ↑) ← 0 ← 1)     🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Apply _) ℕrepr-application-identity ]
        (ℕrepr(X) ↑ ↑) ← 0 ← ℕrepr₂(Y)                    🝖[ _⇴*_ ]-[] -- TODO: ℕrepr-application-identity?
        {!!}           🝖[ _⇴_ ]-[ {!!} ]-sub
        (𝜆 2 (𝜆 3 (ApplyIterated 2 3 X))) ← 0 ← ℕrepr₂(Y) 🝖[ _⇴_ ]-[ cong-applyₗ β ]-sub
        {!!}           🝖[ _⇴_ ]-[ {!!} ]-sub
        (𝜆 2 (ApplyIterated 0 2 X)) ← ℕrepr₂(Y)           🝖[ _⇴_ ]-[ β ]-sub
        {!!}           🝖[ _⇴_ ]-[ {!substituteVar-on-ApplyIterated{i = 𝕟.maximum{3}}{t = ℕrepr₂ Y}{f = 0}{x = 2}{n = X}!} ]-sub
        ApplyIterated 0 (ℕrepr₂(Y)) X                     🝖[ _⇴*_ ]-[ sub₂(_≡_)(_⇴*_) (ApplyIterated-[+] {2}{f = 0}{x = 1}{n₁ = Y}{n₂ = X}) ]
        ApplyIterated 0 1 (Y + X)                         🝖-end
      ))]
      ℕrepr(Y + X) 🝖-end
    ⦄)

  Mul-is-nat : Nat x → Nat y → Nat(Mul ← x ← y)
  Mul-is-nat {x = x}{y = y} ([∃]-intro X ⦃ px ⦄) ([∃]-intro Y ⦃ py ⦄) =
    ([∃]-intro (X ⋅ Y) ⦃
      Mul ← x ← y                                           🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Apply _) py ]
      Mul ← x ← ℕrepr(Y)                                    🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(swap Apply _) (compatible₁(_⇴*_)(_⇴*_)(Apply _) px) ]
      Mul ← ℕrepr(X) ← ℕrepr(Y)                             🝖[ _⇴*_ ]-[]
      (𝜆 0 (𝜆 1 (𝜆 2 (0 ← (1 ← 2))))) ← ℕrepr(X) ← ℕrepr(Y) 🝖[ _⇴_ ]-[ cong-applyₗ β ]-sub
      (𝜆 0 (𝜆 1 ((ℕrepr(X) ↑ ↑) ← (0 ← 1)))) ← ℕrepr(Y)     🝖[ _⇴_ ]-[ {!β!} ]-sub
      𝜆 0 ((ℕrepr(X) ↑) ← ((ℕrepr(Y) ↑) ← 0))               🝖[ _⇴_ ]-[ cong-abstract (cong-applyᵣ β) ]-sub
      {!!}           🝖[ _⇴_ ]-[ {!!} ]-sub
      𝜆 0 ((ℕrepr(X) ↑) ← (𝜆 1 (ApplyIterated 0 1 Y)))      🝖[ _⇴_ ]-[ cong-abstract β ]-sub
      {!!}           🝖[ _⇴_ ]-[ {!!} ]-sub
      𝜆 0 (𝜆 1 (ApplyIterated (𝜆 2 (ApplyIterated 0 2 Y)) 1 X)) 🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Abstract) (compatible₁(_⇴*_)(_⇴*_)(Abstract) (ApplyIterated-[⋅] {i = 1}{n₁ = X})) ]
      ℕrepr(X ⋅ Y) 🝖-end
    ⦄)

  Exp-is-nat : Nat x → Nat y → Nat(Exp ← x ← y)
  Exp-is-nat {x = x}{y = y} ([∃]-intro X ⦃ px ⦄) ([∃]-intro Y ⦃ py ⦄) =
    ([∃]-intro (X ^ Y) ⦃
      Exp ← x ← y                                           🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Apply _) py ]
      Exp ← x ← ℕrepr(Y)                                    🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(swap Apply _) (compatible₁(_⇴*_)(_⇴*_)(Apply _) px) ]
      Exp ← ℕrepr(X) ← ℕrepr(Y)                             🝖[ _⇴*_ ]-[]
      (𝜆 0 (𝜆 1 (1 ← 0))) ← ℕrepr(X) ← ℕrepr(Y)             🝖[ _⇴_ ]-[ cong-applyₗ {!β!} ]-sub
      (𝜆 0 (0 ← (ℕrepr(X) ↑))) ← ℕrepr(Y)                   🝖[ _⇴_ ]-[ β ]-sub
      ℕrepr(Y) ← ℕrepr(X)                                   🝖[ _⇴*_ ]-[]
      (𝜆 0 (𝜆 1 (ApplyIterated 0 1 Y))) ← (𝜆 0 (𝜆 1 (ApplyIterated 0 1 X))) 🝖[ _⇴_ ]-[ β ]-sub
      {!!}           🝖[ _⇴_ ]-[ {!!} ]-sub
      𝜆 0 (ApplyIterated (𝜆 1 (𝜆 2 (ApplyIterated 1 2 X))) 0 Y)             🝖[ _⇴*_ ]-[ {!Exp ← ℕrepr(X) ← ℕrepr(Y)!} ]
      ℕrepr(X ^ Y) 🝖-end
    ⦄)

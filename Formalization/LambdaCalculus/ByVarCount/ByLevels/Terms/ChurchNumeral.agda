-- Natural numbers using the "Church numerals"-representation.
-- Note: This module needs the `cong-abstract` reduction rule to work.
module Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.ChurchNumeral where

import      Lvl
open import Data
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.Functions using () renaming (varShift𝐒₀ to _↑)
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.ApplyIterated hiding (module Proofs)
open        Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.ApplyIterated.Proofs
import      Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Boolean as Bool
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators using (K ; 𝈲)
open import Formalization.LambdaCalculus.ByVarCount.Syntax.ExplicitLambda
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

𝐏 = 𝜆 0 (𝜆 1 (𝜆 2 (0 ← (𝜆 3 (𝜆 4 (4 ← (3 ← 1)))) ← (𝜆 3 2) ← (𝜆 3 3)))) -- Predecessor
IsZero = 𝜆 0 (0 ← (𝜆 1 (Bool.𝐹 ↑ ↑)) ← (Bool.𝑇 ↑))

ℕrepr₂ = ApplyIterated{2} 0 1
ℕrepr = \n → 𝜆 0 (𝜆 1 (ℕrepr₂ n))

module Proofs where
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction.Proofs
  open import Formalization.LambdaCalculus.ByVarCount.Functions renaming (varShift𝐒ᵢ to _↑ᵢ ; varShift𝐒Outermost to _↑')
  open import Formalization.LambdaCalculus.ByVarCount.Functions.Proofs
  open        Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators.Proofs using (K-reduction ; 𝈲-reduction)
  open import Functional using (swap)
  open import Numeral.Finite as 𝕟 using (𝕟)
  open import Numeral.Natural as ℕ using (ℕ)
  open import Numeral.Natural.Oper
  open import Numeral.Natural.Oper.Proofs
  import      Numeral.Natural.Relation as ℕ
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv
  open import Relator.ReflexiveTransitiveClosure
  open import Relator.ReflexiveTransitiveClosure.Proofs
  open import Structure.Function
  open import Structure.Operator
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  private variable n n₁ n₂ : ℕ
  private variable i : 𝕟(n)
  private variable f g h t x y z x₁ x₂ y₁ y₂ : Term(n)

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

  ℕrepr-application-to-ApplyIterated : (ℕrepr(n) ← x ← y) ⇴* ApplyIterated x y n
  ℕrepr-application-to-ApplyIterated {n = n}{x = x}{y = y} =
    ℕrepr(n) ← x ← y                          🝖[ _⇴*_ ]-[]
    (𝜆 0 (𝜆 1 (ApplyIterated 0 1 n))) ← x ← y 🝖[ _⇴_ ]-[ cong-applyₗ β ]-sub
    (𝜆 0 (ApplyIterated (x ↑) 0 n)) ← y       🝖[ _⇴_ ]-[ β ]-sub
    ApplyIterated x y n                       🝖-end

  -- TODO: Same proof as ℕrepr-application-to-ApplyIterated
  ℕrepr-application-identity : ((ℕrepr(n) ↑ ↑) ← 0 ← 1) ⇴* ℕrepr₂(n)
  ℕrepr-application-identity {n = n} =
    (ℕrepr(n) ↑ ↑) ← 0 ← 1                    🝖[ _⇴*_ ]-[]
    (𝜆 2 (𝜆 3 (ApplyIterated 2 3 n))) ← 0 ← 1 🝖[ _⇴_ ]-[ cong-applyₗ β ]-sub
    (𝜆 2 (ApplyIterated 0 2 n)) ← 1           🝖[ _⇴_ ]-[ β ]-sub
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
        (𝜆 2 (𝜆 3 (ApplyIterated 2 3 X))) ← 0 ← ℕrepr₂(Y) 🝖[ _⇴_ ]-[ cong-applyₗ β ]-sub
        (𝜆 2 (ApplyIterated 0 2 X)) ← ℕrepr₂(Y)           🝖[ _⇴_ ]-[ β ]-sub
        ApplyIterated 0 (ℕrepr₂(Y)) X                     🝖[ _⇴*_ ]-[ sub₂(_≡_)(_⇴*_) (ApplyIterated-[+] {2}{f = 0}{x = 1}{n₁ = Y}{n₂ = X}) ]
        ApplyIterated 0 1 (Y + X)                         🝖-end
      ))]
      ℕrepr(Y + X) 🝖-end
    ⦄)

  Mul-is-nat : Nat x → Nat y → Nat(Mul ← x ← y)
  Mul-is-nat {x = x}{y = y} ([∃]-intro X ⦃ px ⦄) ([∃]-intro Y ⦃ py ⦄) =
    ([∃]-intro (X ⋅ Y) ⦃
      Mul ← x ← y                                                          🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Apply _) py ]
      Mul ← x ← ℕrepr(Y)                                                   🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(swap Apply _) (compatible₁(_⇴*_)(_⇴*_)(Apply _) px) ]
      Mul ← ℕrepr(X) ← ℕrepr(Y)                                            🝖[ _⇴*_ ]-[]
      (𝜆 0 (𝜆 1 (𝜆 2 (0 ← (1 ← 2))))) ← ℕrepr(X) ← ℕrepr(Y)                🝖[ _⇴_ ]-[ cong-applyₗ β ]-sub
      (𝜆 0 (𝜆 1 ((ℕrepr(X) ↑ ↑) ← (0 ← 1)))) ← ℕrepr(Y)                    🝖[ _⇴_ ]-[ cong-applyₗ (cong-abstract (cong-abstract β)) ]-sub
      (𝜆 0 (𝜆 1 (𝜆 2 (ApplyIterated(0 ← 1) 2 X)))) ← ℕrepr(Y)              🝖[ _⇴_ ]-[ β ]-sub
      𝜆 0 (𝜆 1 (ApplyIterated((ℕrepr(Y) ↑ ↑) ← 0) 1 X))                    🝖[ _⇴*_ ]-[]
      𝜆 0 (𝜆 1 (ApplyIterated((𝜆 2 (𝜆 3 (ApplyIterated 2 3 Y))) ← 0) 1 X)) 🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Abstract) (compatible₁(_⇴*_)(_⇴*_)(Abstract) (compatible₁(_⇴*_)(_⇴*_)(_) ⦃ [⇴*]-ApplyIteratedₗ-function {n = X} ⦄ (sub₂(_⇴_)(_⇴*_) β))) ]
      𝜆 0 (𝜆 1 (ApplyIterated (𝜆 2 (ApplyIterated 0 2 Y)) 1 X))            🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Abstract) (compatible₁(_⇴*_)(_⇴*_)(Abstract) (ApplyIterated-[⋅] {n₁ = X})) ]
      ℕrepr(X ⋅ Y)                                                         🝖-end
    ⦄)

  {- TODO: Exp-is-nat : Nat x → Nat y → Nat(Exp ← x ← y)
  Exp-is-nat {x = x}{y = y} ([∃]-intro X ⦃ px ⦄) ([∃]-intro Y ⦃ py ⦄) =
    ([∃]-intro (X ^ Y) ⦃
      Exp ← x ← y                                           🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(Apply _) py ]
      Exp ← x ← ℕrepr(Y)                                    🝖[ _⇴*_ ]-[ compatible₁(_⇴*_)(_⇴*_)(swap Apply _) (compatible₁(_⇴*_)(_⇴*_)(Apply _) px) ]
      Exp ← ℕrepr(X) ← ℕrepr(Y)                             🝖[ _⇴*_ ]-[]
      (𝜆 0 (𝜆 1 (1 ← 0))) ← ℕrepr(X) ← ℕrepr(Y)             🝖[ _⇴_ ]-[ cong-applyₗ β ]-sub
      (𝜆 0 (0 ← (ℕrepr(X) ↑))) ← ℕrepr(Y)                   🝖[ _⇴_ ]-[ β ]-sub
      ℕrepr(Y) ← ℕrepr(X)                                   🝖[ _⇴*_ ]-[]
      (𝜆 0 (𝜆 1 (ApplyIterated 0 1 Y))) ← (𝜆 0 (𝜆 1 (ApplyIterated 0 1 X))) 🝖[ _⇴_ ]-[ β ]-sub
      𝜆 0 (ApplyIterated (𝜆 1 (𝜆 2 (ApplyIterated 1 2 X))) 0 Y)             🝖[ _⇴*_ ]-[ {!Exp ← ℕrepr(X) ← ℕrepr(Y)!} ]
      ℕrepr(X ^ Y) 🝖-end
    ⦄)
-}

{-
(x → f) (x → f) (x → f)
(subst (x → f) f) (x → f)

(𝜆 1 (𝜆 2 (ApplyIterated 1 2 X))) (𝜆 1 (𝜆 2 (ApplyIterated 1 2 X))) (𝜆 1 (𝜆 2 (ApplyIterated 1 2 X)))
(𝜆 1 (ApplyIterated (𝜆 2 (𝜆 3 (ApplyIterated 2 3 X))) 1 X)) (𝜆 1 (𝜆 2 (ApplyIterated 1 2 X)))
ApplyIterated (𝜆 1 (𝜆 2 (ApplyIterated 1 2 X))) (𝜆 1 (𝜆 2 (ApplyIterated 1 2 X))) X
-}

module Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Boolean where

import      Lvl
open import Data
open import Formalization.LambdaCalculus.ByVarCount
open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators using (K ; 𝈲)
open import Formalization.LambdaCalculus.ByVarCount.Syntax.ExplicitLambda
open import Formalization.LambdaCalculus.ByVarCount.Functions renaming (varShift𝐒₀ to _↑₀ ; varShift𝐒₁ to _↑₁ ; varShift𝐒ᵢ to _↑)
open import Syntax.Number
open import Type

𝑇   = K                           -- True (constructor)
𝐹   = 𝈲                           -- False (constructor)
If  = 𝜆 0 (𝜆 1 (𝜆 2 (0 ← 1 ← 2))) -- If-else (extractor)
Not = 𝜆 0 ((If ↑₀) ← 0 ← (𝐹 ↑₀) ← (𝑇 ↑₀))
And = 𝜆 0 (𝜆 1 ((If ↑₀ ↑₁) ← 0 ← 1 ← 0))
Or  = 𝜆 0 (𝜆 1 ((If ↑₀ ↑₁) ← 0 ← 0 ← 1))

module Proofs where
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction
  open import Formalization.LambdaCalculus.ByVarCount.ByLevels.Semantics.Reduction.Proofs
  open        Formalization.LambdaCalculus.ByVarCount.ByLevels.Terms.Combinators.Proofs using (K-reduction ; 𝈲-reduction)
  open import Logic.Propositional hiding (_←_)
  open import Numeral.Natural
  open import Structure.Function
  open import Structure.Relator.Properties
  open import Syntax.Transitivity

  private variable n : ℕ
  private variable f g h x y z : Term(n)

  Bool : Expression → Type
  Bool(t) = (t β⇴* 𝑇) ∨ (t β⇴* 𝐹)

  β⇴*-Bool-swap-sub : (x β⇴* y) → (Bool(y) → Bool(x))
  β⇴*-Bool-swap-sub xy = [∨]-elim2 (xy 🝖_) (xy 🝖_)

  𝑇-is-bool : Bool(𝑇)
  𝑇-is-bool = [∨]-introₗ (reflexivity(_β⇴*_))

  𝐹-is-bool : Bool(𝐹)
  𝐹-is-bool = [∨]-introᵣ (reflexivity(_β⇴*_))

  If-𝑇-reduction : ((If ← 𝑇 ← x ← y) β⇴* x)
  If-𝑇-reduction{x}{y} =
    (𝜆 0 (𝜆 1 (𝜆 2 (0 ← 1 ← 2)))) ← K ← x ← y 🝖-[ (cong-applyₗ(cong-applyₗ β)) ]-sub
    𝜆 0 (𝜆 1 ((K ↑₀ ↑₁) ← 0 ← 1)) ← x ← y     🝖-[ (cong-applyₗ β) ]-sub
    (𝜆 0 ((K ↑₀) ← (x ↑) ← 0)) ← y            🝖-[ β ]-sub
    K ← x ← y                                 🝖-[ K-reduction ]
    x                                         🝖-end

  If-𝐹-reduction : ((If ← 𝐹 ← x ← y) β⇴* y)
  If-𝐹-reduction{x}{y} = 
    (𝜆 0 (𝜆 1 (𝜆 2 (0 ← 1 ← 2)))) ← 𝈲 ← x ← y 🝖-[ cong-applyₗ(cong-applyₗ β) ]-sub
    𝜆 0 (𝜆 1 ((𝈲 ↑₀ ↑₁) ← 0 ← 1)) ← x ← y     🝖-[ cong-applyₗ β ]-sub
    (𝜆 0 ((𝈲 ↑₀) ← (x ↑) ← 0)) ← y            🝖-[ β ]-sub
    𝈲 ← x ← y                                 🝖-[ 𝈲-reduction ]
    y                                         🝖-end

  If-is-bool : Bool(x) → Bool(y) → Bool(z) → Bool(If ← x ← y ← z)
  If-is-bool {x}{y}{z} ([∨]-introₗ p) q r = β⇴*-Bool-swap-sub
    (compatible₁ _ _ (\f → Apply f _) (compatible₁ _ _ (\f → Apply f _) (compatible₁ _ _ (\x → Apply _ x) p)))
    ([∨]-elim2 (If-𝑇-reduction 🝖_) (If-𝑇-reduction 🝖_) q)
  If-is-bool {x}{y}{z} ([∨]-introᵣ p) q r = β⇴*-Bool-swap-sub
    (compatible₁ _ _ (\f → Apply f _) (compatible₁ _ _ (\f → Apply f _) (compatible₁ _ _ (\x → Apply _ x) p)))
    ([∨]-elim2 (If-𝐹-reduction 🝖_) (If-𝐹-reduction 🝖_) r)

  Not-𝑇-reduction : ((Not ← 𝑇) β⇴* 𝐹)
  Not-𝑇-reduction =
    Not ← 𝑇        🝖-[ β ]-sub
    If ← 𝑇 ← 𝐹 ← 𝑇 🝖-[ If-𝑇-reduction ]
    𝐹              🝖-end

  Not-𝐹-reduction : ((Not ← 𝐹) β⇴* 𝑇)
  Not-𝐹-reduction =
    Not ← 𝐹        🝖-[ β ]-sub
    If ← 𝐹 ← 𝐹 ← 𝑇 🝖-[ If-𝐹-reduction ]
    𝑇              🝖-end

  Not-is-bool : Bool(x) → Bool(Not ← x)
  Not-is-bool ([∨]-introₗ p) = [∨]-introᵣ (compatible₁ _ _ (\x → Apply _ x) p 🝖 Not-𝑇-reduction)
  Not-is-bool ([∨]-introᵣ p) = [∨]-introₗ (compatible₁ _ _ (\x → Apply _ x) p 🝖 Not-𝐹-reduction)

  And-𝑇-reduction : ((And ← 𝑇 ← x) β⇴* x)
  And-𝑇-reduction {x} =
    And ← 𝑇 ← x                               🝖-[ cong-applyₗ β ]-sub
    (𝜆 0 ((If ↑₀) ← (𝑇 ↑₀) ← 0 ← (𝑇 ↑₀))) ← x 🝖-[ β ]-sub
    If ← 𝑇 ← x ← 𝑇                            🝖-[ If-𝑇-reduction ]
    x                                         🝖-end

  And-𝐹-reduction : ((And ← 𝐹 ← x) β⇴* 𝐹)
  And-𝐹-reduction {x} =
    And ← 𝐹 ← x                               🝖-[ cong-applyₗ β ]-sub
    (𝜆 0 ((If ↑₀) ← (𝐹 ↑₀) ← 0 ← (𝐹 ↑₀))) ← x 🝖-[ β ]-sub
    If ← 𝐹 ← x ← 𝐹                            🝖-[ If-𝐹-reduction ]
    𝐹                                         🝖-end

  And-is-bool : Bool(x) → Bool(y) → Bool(And ← x ← y)
  And-is-bool {x}{y} bx by = β⇴*-Bool-swap-sub
    (
      And ← x ← y                               🝖-[ compatible₁ _ _ (\f → Apply f _) β ]-sub
      (𝜆 0 ((If ↑₀) ← (x ↑₀) ← 0 ← (x ↑₀))) ← y 🝖-[ β ]-sub
      If ← x ← y ← x 🝖-end
    )
    (If-is-bool bx by bx)

  Or-𝐹-reduction : ((Or ← 𝐹 ← x) β⇴* x)
  Or-𝐹-reduction {x = x} =
    Or ← 𝐹 ← x                                🝖-[ cong-applyₗ β ]-sub
    (𝜆 0 ((If ↑₀) ← (𝐹 ↑₀) ← (𝐹 ↑₀) ← 0)) ← x 🝖-[ β ]-sub
    If ← 𝐹 ← 𝐹 ← x                            🝖-[ If-𝐹-reduction ]
    x                                         🝖-end

  Or-𝑇-reduction : ((Or ← 𝑇 ← x) β⇴* 𝑇)
  Or-𝑇-reduction {x = x} =
    Or ← 𝑇 ← x                                🝖-[ cong-applyₗ β ]-sub
    (𝜆 0 ((If ↑₀) ← (𝑇 ↑₀) ← (𝑇 ↑₀) ← 0)) ← x 🝖-[ β ]-sub
    If ← 𝑇 ← 𝑇 ← x                            🝖-[ If-𝑇-reduction ]
    𝑇                                         🝖-end

  Or-is-bool : Bool(x) → Bool(y) → Bool(Or ← x ← y)
  Or-is-bool {x}{y} bx by = β⇴*-Bool-swap-sub
    (
      Or ← x ← y                                🝖-[ compatible₁ _ _ (\f → Apply f _) β ]-sub
      (𝜆 0 ((If ↑₀) ← (x ↑₀) ← (x ↑₀) ← 0)) ← y 🝖-[ β ]-sub
      If ← x ← x ← y 🝖-end
    )
    (If-is-bool bx bx by)

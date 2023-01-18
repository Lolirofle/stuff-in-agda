module Structure.Setoid.Size.Properties.Choice where

open import Logic
import      Lvl
open import Structure.Setoid
open import Structure.Setoid.Size

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₗ : Lvl.Level

-- This is variant of the "extensional axiom of choice" and the general principle for all setoids is unprovable in Agda, though it is a possible axiom.
-- Note: This has not actually been proven to be equialent to axiom of choice. It has been proven that AC implies this though
-- A proof of `(A ≽ B)` means that a right inverse exist, but if the surjection is non-injective (it could be in general), then the right inverse is not a function (two equal values in the codomain of the surjection may point to two inequal objects in the domain).
-- Example:
--   For X: Set, Y: Set, f: X → Y, a: X, b: X, c₁: Y, c₂: Y
--   Assume:
--     X = {a,b}
--     Y = {c₁,c₂}
--     a ≢ b
--     c₁ ≡ c₂
--     f(a) = c₁
--     f(b) = c₂
--   This means that f is surjective (maps to both c₁ and c₂) but not injective ((c₁ ≡ c₂) implies (f(a) ≡ f(b)) implies (a ≡ b) which is false).
--   Then an inverse f⁻¹ to f can be constructed from the witnesses in surjectivity:
--     f⁻¹: Y → X
--     f⁻¹(c₁) = a
--     f⁻¹(c₂) = b
--   f⁻¹ is obviously injective, but it is also not a function: ((c₁ ≡ c₂) would imply (a ≡ b) if it were a function, but that is false).
--   This example shows that not all surjections are injective.
--   But looking at the example, there are functions that are injective:
--     g₁: Y → X
--     g₁(c₁) = a
--     g₁(c₂) = a
--
--     g₂: Y → X
--     g₂(c₁) = b
--     g₂(c₂) = b
--   They are, because: ((a ≡ a) implies (g₁(c₁) ≡ g₁(c₂)) implies (c₁ ≡ c₂) which is true).
--   and              : ((b ≡ b) implies (g₂(c₁) ≡ g₂(c₂)) implies (c₁ ≡ c₂) which is true).
--   This is a simplified example using finite sets, and a restriction of this proposition for finite sets is actually provable because it is possible to enumerate all functions up to function extensionality and check all of them in finite time.
--   The real problem comes when the sets are non-finite because then, there are no general methods to enumerate the elements. How would an injection be chosen in those cases?
-- Note that if the surjection is injective, then it is a bijection, and therefore also an injection.
-- Also called: Partition principle.
record SurjectionInjectionChoice (A : Setoid{ℓₑ₁}{ℓ₁}) (B : Setoid{ℓₑ₂}{ℓ₂}) : Stmt{ℓₑ₁ Lvl.⊔ ℓ₁ Lvl.⊔ ℓₑ₂ Lvl.⊔ ℓ₂} where
  constructor intro
  field proof : (A ≽ B) → (B ≼ A)
open SurjectionInjectionChoice ⦃ … ⦄ using () renaming (proof to [≽]-to-[≼]) public

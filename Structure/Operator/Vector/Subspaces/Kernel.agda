import      Lvl
open import Structure.Setoid
open import Type

module Structure.Operator.Vector.Subspaces.Kernel
  {ℓₛ ℓₛₑ}
  {S : Type{ℓₛ}}
  ⦃ equiv-S : Equiv{ℓₛₑ}(S) ⦄
  {_+ₛ_ _⋅ₛ_ : S → S → S}
  where

open import Logic.Predicate
open import Sets.ExtensionalPredicateSet as PredSet using (PredSet ; _∈_ ; [∋]-binaryRelator)
open import Structure.Container.SetLike as SetLike using (SetElement)
open import Structure.Function.Multi
open import Structure.Operator
open import Structure.Operator.Properties
open import Structure.Operator.Vector
open import Structure.Operator.Vector.LinearMap
open import Structure.Operator.Vector.Proofs
open import Structure.Operator.Vector.Subspace
open import Structure.Relator.Properties
open import Syntax.Implication
open import Syntax.Transitivity

open VectorSpace ⦃ … ⦄
open VectorSpaceVObject ⦃ … ⦄ using (_+ᵥ_; _⋅ₛᵥ_)
open VectorSpaceVObject       using (Vector)

private variable ℓ ℓᵥ ℓᵥₑ : Lvl.Level
private variable V W : VectorSpaceVObject {ℓᵥ = ℓᵥ} {ℓᵥₑ = ℓᵥₑ} ⦃ equiv-S = equiv-S ⦄ (_+ₛ_)(_⋅ₛ_)
private variable F : V →ˡⁱⁿᵉᵃʳᵐᵃᵖ W

kernel : (V →ˡⁱⁿᵉᵃʳᵐᵃᵖ W) → PredSet(Vector(V))
kernel {V = V}{W = W} ([∃]-intro f) = PredSet.unapply f(𝟎ᵥ)

kernel-subspace : Subspace(kernel(F))
SetLike.FunctionProperties._closed-under₂_.proof (Subspace.add-closure (kernel-subspace {_} {_} {V} {_} {_} {W} {F = F@([∃]-intro f)})) {x} {y} xkern ykern =
  • (
    xkern         ⇒
    x ∈ kernel(F) ⇒-[]
    f(x) ≡ 𝟎ᵥ     ⇒-end
  )
  • (
    ykern         ⇒
    y ∈ kernel(F) ⇒-[]
    f(y) ≡ 𝟎ᵥ     ⇒-end
  )                       ⇒₂-[ congruence₂{A₁ = Vector(W)}{A₂ = Vector(W)}(_+ᵥ_) ]
  f(x) +ᵥ f(y) ≡ 𝟎ᵥ +ᵥ 𝟎ᵥ ⇒-[ _🝖 identityᵣ(_+ᵥ_)(𝟎ᵥ) ]
  f(x) +ᵥ f(y) ≡ 𝟎ᵥ       ⇒-[ preserving₂(f)(_+ᵥ_)(_+ᵥ_) 🝖_ ]
  f(x +ᵥ y) ≡ 𝟎ᵥ          ⇒-[]
  (x +ᵥ y) ∈ kernel(F)    ⇒-end
  where
    instance _ = V
    instance _ = W
SetLike.FunctionProperties._closed-under₁_.proof (Subspace.mul-closure (kernel-subspace {_}{_}{V}{_}{_}{W} {F = F@([∃]-intro f)}) {s}) {v} vkern =
  vkern ⇒
  v ∈ kernel(F)         ⇒-[]
  f(v) ≡ 𝟎ᵥ             ⇒-[ congruence₂ᵣ(_⋅ₛᵥ_)(s) ]
  s ⋅ₛᵥ f(v) ≡ s ⋅ₛᵥ 𝟎ᵥ ⇒-[ _🝖 [⋅ₛᵥ]-absorberᵣ ]
  s ⋅ₛᵥ f(v) ≡ 𝟎ᵥ       ⇒-[ preserving₁(f)(s ⋅ₛᵥ_)(s ⋅ₛᵥ_) 🝖_ ]
  f(s ⋅ₛᵥ v) ≡ 𝟎ᵥ       ⇒-[]
  (s ⋅ₛᵥ v) ∈ kernel(F) ⇒-end
  where
    instance _ = V
    instance _ = W

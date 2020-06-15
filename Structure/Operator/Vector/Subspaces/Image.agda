import      Lvl
open import Structure.Setoid.WithLvl
open import Type

module Structure.Operator.Vector.Subspaces.Image
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
open import Syntax.Function
open import Syntax.Implication
open import Syntax.Transitivity

open VectorSpace ⦃ … ⦄
open VectorSpaceVObject ⦃ … ⦄ using (_+ᵥ_; _⋅ₛᵥ_)
open VectorSpaceVObject       using (Vector)

private variable ℓ ℓᵥ ℓᵥₑ : Lvl.Level
private variable V W : VectorSpaceVObject {ℓᵥ = ℓᵥ} {ℓᵥₑ = ℓᵥₑ} ⦃ equiv-S = equiv-S ⦄ (_+ₛ_)(_⋅ₛ_)
private variable F : V →ˡⁱⁿᵉᵃʳᵐᵃᵖ W

image : (V →ˡⁱⁿᵉᵃʳᵐᵃᵖ W) → PredSet(Vector(W))
image {V = V}{W = W} ([∃]-intro f) = PredSet.⊶ f

image-subspace : Subspace(image(F))
SetLike.FunctionProperties._closed-under₂_.proof (Subspace.add-closure (image-subspace {_} {_} {V} {_} {_} {W} {F = F@([∃]-intro f)})) {x} {y} xim yim =
  • (
    xim             ⇒
    x ∈ image(F)    ⇒-[]
    ∃(a ↦ f(a) ≡ x) ⇒-end
  )
  • (
    yim             ⇒
    y ∈ image(F)    ⇒-[]
    ∃(a ↦ f(a) ≡ y) ⇒-end
  )                      ⇒₂-[ [∃]-map₂ (_+ᵥ_) (p ↦ q ↦ (preserving₂(f)(_+ᵥ_)(_+ᵥ_) 🝖 congruence₂(_+ᵥ_) p q)) ]
  ∃(a ↦ f(a) ≡ x +ᵥ y)   ⇒-[]
  (x +ᵥ y) ∈ image(F)    ⇒-end
  where
    instance _ = V
    instance _ = W
SetLike.FunctionProperties._closed-under₁_.proof (Subspace.mul-closure (image-subspace {_} {_} {V} {_} {_} {W} {F = F@([∃]-intro f)}) {s}) {v} vim =
  vim ⇒
  v ∈ image(F)                ⇒-[]
  ∃(x ↦ f(x) ≡ v)             ⇒-[ [∃]-map-proof (congruence₂ᵣ(_⋅ₛᵥ_)(s)) ]
  ∃(x ↦ s ⋅ₛᵥ f(x) ≡ s ⋅ₛᵥ v) ⇒-[ [∃]-map (s ⋅ₛᵥ_) (preserving₁(f)(s ⋅ₛᵥ_)(s ⋅ₛᵥ_) 🝖_) ]
  ∃(x ↦ f(x) ≡ s ⋅ₛᵥ v)       ⇒-[]
  (s ⋅ₛᵥ v) ∈ image(F)        ⇒-end
  where
    instance _ = V
    instance _ = W

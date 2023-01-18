module Numeral.Finite.Category where

open import Numeral.Finite
open import Numeral.Natural

open import Functional
import      Lvl
open import Type
open import Syntax.Function

-- Equality category on the type of finite natural numbers.
module _ where
  open import Relator.Equals
  open import Relator.Equals.Proofs.Equiv
  open import Relator.Equals.Category
  open import Structure.Category
  open import Structure.Category.Categories
  import      Structure.Category.Functor as Category
  open import Structure.Function
  open import Structure.Function.Domain
  import      Structure.Function.Names as Names
  open import Structure.Groupoid
  open import Structure.Groupoid.Groupoids
  import      Structure.Groupoid.Functor as Groupoid

  𝕟-identityTypeGroupoid : Groupoid((_≡_) on₂ 𝕟)
  𝕟-identityTypeGroupoid = on₂-groupoid identityTypeGroupoid 𝕟

  -- The type constructor `𝕟` is a functor.
  -- This means:
  -- • `map: ∀(a: ℕ)(b: ℕ). (a ≡ b) → (𝕟(a) ≡ 𝕟(b))`
  -- • `map(reflexivity(_≡_)) ≡ reflexivity(_≡_)`
  -- • `transitivity(_≡_) (map p) (map q) ≡ map(transitivity(_≡_) p q)`
  𝕟-functor : Groupoid.Functor(identityTypeGroupoid{T = ℕ})(𝕟-identityTypeGroupoid) id
  𝕟-functor = idTransportFunctor

  {- TODO: This works when using the INJECTIVE pragma on 𝕟 because injective(𝕟) becomes equal definitionally
  instance
    𝕟-injectivity : Injective(𝕟)
    𝕟-injectivity = intro proof where
      proof : Names.Injective(𝕟)
      proof {𝟎}   {𝟎}    [≡]-intro = [≡]-intro
      proof {𝐒 a} {𝐒 .a} [≡]-intro = congruence₁(𝐒) (proof [≡]-intro)

  𝕟-inverse-functor : Groupoid.Functor(𝕟-identityTypeGroupoid)(identityTypeGroupoid{T = ℕ}) id
  Groupoid.Functor.map 𝕟-inverse-functor = injective(𝕟)
  Function.congruence (Groupoid.Functor.map-function 𝕟-inverse-functor) [≡]-intro = [≡]-intro
  Groupoid.Functor.op-preserving 𝕟-inverse-functor {x} {x} {x} {[≡]-intro} {[≡]-intro} = proof{x} where
    proof : ∀{x} → Groupoid.Functor.map 𝕟-inverse-functor (Groupoid._∘_ 𝕟-identityTypeGroupoid {x} [≡]-intro [≡]-intro) ≡ Groupoid._∘_ identityTypeGroupoid (Groupoid.Functor.map 𝕟-inverse-functor [≡]-intro) (Groupoid.Functor.map 𝕟-inverse-functor [≡]-intro)
    proof {𝟎} = [≡]-intro
    proof {𝐒 x}
      rewrite proof{x}
      rewrite Groupoid.Functor.id-preserving 𝕟-inverse-functor {x}
      = [≡]-intro
  Groupoid.Functor.id-preserving 𝕟-inverse-functor {x} = proof{x} where
    proof : ∀{x} → (injective(𝕟) (Groupoid.id 𝕟-identityTypeGroupoid {x}) ≡ Category.id identityTypeCategory)
    proof {𝟎} = [≡]-intro
    proof {𝐒 x} rewrite proof{x} = [≡]-intro
  Groupoid.Functor.inv-preserving 𝕟-inverse-functor {x} {x} {[≡]-intro} = proof where
    proof : ∀{x} → Groupoid.Functor.map 𝕟-inverse-functor (Groupoid.inv 𝕟-identityTypeGroupoid {x} [≡]-intro) ≡ Groupoid.inv identityTypeGroupoid (Groupoid.Functor.map 𝕟-inverse-functor [≡]-intro)
    proof {𝟎} = [≡]-intro
    proof {𝐒 x}
      rewrite proof{x}
      rewrite Groupoid.Functor.id-preserving 𝕟-inverse-functor {x}
      = [≡]-intro
  -}

  open import Function.Equals
  open import Numeral.Finite.Bound
  open import Numeral.Natural.Relation.Order.Category
  open import Numeral.Natural.Relation.Order.Proofs
  open import Numeral.Natural.Relation.Order
  open import Type.Category.FakeExtensionalFunctionsCategory
  open import Structure.Categorical.Functor.Properties
  open import Structure.Relator.Properties

  -- A functor for boundary changing of finite numeral types (𝕟).
  bound-functor : Category.Functor [≤]-category (on₂-category typeFakeExtensionalFnCategory 𝕟) id
  Category.Functor.map bound-functor = bound-[≤]
  Function.congruence (Category.Functor.map-function bound-functor) [≡]-intro = reflexivity(_⊜_)
  Category.Functor.op-preserving bound-functor {x}{y}{z} = intro \{p}{q} → proof{x}{y}{z} {p}{q} where
    proof : ∀{x y z}{p : (y ≤ z)}{q : (x ≤ y)} → (bound-[≤] (transitivity(_≤_) q p) ⊜ (bound-[≤] p) ∘ (bound-[≤] q))
    _⊜_.proof (proof {𝐒 x} {𝐒 y} {𝐒 z} {succ _}  {succ _})  {𝟎}   = [≡]-intro
    _⊜_.proof (proof {𝐒 x} {𝐒 y} {𝐒 z} {succ yz} {succ xy}) {𝐒 n} = congruence₁(𝐒) (_⊜_.proof (proof {x}{y}{z} {yz}{xy}) {n})
  Category.Functor.id-preserving bound-functor {n} = intro(proof{n}) where
    proof : ∀{n} → (bound-[≤] (reflexivity(_≤_) {n}) ⊜ id)
    _⊜_.proof (proof {𝟎})   {()}
    _⊜_.proof (proof {𝐒 n}) {𝟎}   = [≡]-intro
    _⊜_.proof (proof {𝐒 n}) {𝐒 x} = congruence₁(𝐒) (_⊜_.proof (proof {n}) {x})

{-# OPTIONS --cubical #-}

module Type.Cubical.Path.Univalence where

open import BidirectionalFunction using (_↔_ ; _$ₗ_ ; _$ᵣ_ ; intro)
open import Function
open import Logic.Predicate
import      Lvl
open import Lvl.Up.Proofs
open import Structure.Categorical.Functor.Properties
open import Structure.Function
open import Structure.Function.Domain
import      Structure.Function.Names as Names
open import Structure.IndexedOperator.Properties.Preserving using (intro)
open import Structure.Relator.Properties
open import Structure.Type.Identity
open import Syntax.Transitivity
open import Type.Cubical.Glue
open import Type.Cubical.Isomorphism
open import Type.Cubical.Isomorphism.Equiv
open import Type.Cubical.Isomorphism.Proofs
open import Type.Cubical.Path
open import Type.Cubical.Path.Equality
open import Type.Cubical.Sub
open import Type.Cubical
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ : Lvl.Level
private variable T A B P Q : Type{ℓ}

module _
  (_≡_ : Type{ℓ} → Type{ℓ} → Type{ℓₑ})
  ⦃ [≡]-refl   : Reflexivity(_≡_) ⦄
  ⦃ [≡]-idElim : IdentityEliminator(_≡_) {ℓₑ} ⦄
  (ext : ∀{A B} → Path A B ↔ (A ≡ B))
  ⦃ extₗ-preserves-refl : ∀{T} → Preserving₀(_≡_)(Path) (ext $ₗ_) (reflexivity(_≡_)) (reflexivity(Path) {x = T}) ⦄
  ⦃ extᵣ-preserves-refl : ∀{T} → Preserving₀(Path)(_≡_) (ext $ᵣ_) (reflexivity(Path)) (reflexivity(_≡_) {x = T}) ⦄
  where

  -- Path is isomorphic to binary relations when they are reflexive, have an identity eliminator, and when there is a reflexivity preserving mapping in each direction between them.
  -- Another way of seeing this: A bidirectional pair of unital magmoid (non-associative category) functors are always inverses of each other when the preconditions above are satisfied.
  Path-isomorphisms : Path A B ≍ (A ≡ B)
  Path-isomorphisms = [∃]-intro ext where
    instance
      inv : InversePair(ext)
      InversePair.left  inv = intro \{iso}  → idElim(_≡_) (Names.InversePairOnᵣ(ext))
        (
          (ext $ᵣ ext $ₗ reflexivity(_≡_)) 🝖[ Path ]-[ congruence₁(ext $ᵣ_) (preserving₀(_≡_)(Path) (ext $ₗ_) (reflexivity(_≡_)) (reflexivity(Path))) ]
          (ext $ᵣ reflexivity(Path))       🝖[ Path ]-[ preserving₀(Path)(_≡_) (ext $ᵣ_) (reflexivity(Path)) (reflexivity(_≡_)) ]
          reflexivity(_≡_)                 🝖-end
        )
        iso
      InversePair.right inv = intro \{path} → idElim(Path) (Names.InversePairOnₗ(ext))
        (
          (ext $ₗ ext $ᵣ reflexivity(Path)) 🝖[ Path ]-[ congruence₁(ext $ₗ_) (preserving₀(Path)(_≡_) (ext $ᵣ_) (reflexivity(Path)) (reflexivity(_≡_))) ]
          (ext $ₗ reflexivity(_≡_))         🝖[ Path ]-[ preserving₀(_≡_)(Path) (ext $ₗ_) (reflexivity(_≡_)) (reflexivity(Path)) ]
          reflexivity(Path)                 🝖-end
        )
        path

-- The existence of a path between types is equivalent to them being isomorphic.
-- TODO: Are these actually category functors? Below are proofs that they preserve reflexivity. Is it possible to also prove that they preserve transitivity?
type-extensionality : Path A B ↔ (A ≍ B)
type-extensionality = intro l r where
  l : Path A B ← (A ≍ B)
  l {A = A}{B = B} ab i = primGlue(B)
    (\{(i = Interval.𝟎) → A  ; (i = Interval.𝟏) → B})
    (\{(i = Interval.𝟎) → ab ; (i = Interval.𝟏) → reflexivity(_≍_)})

  r : Path A B → (A ≍ B)
  r ab = interval-predicate-isomorphism(\i → ab i)
  -- sub₂(Path)(_≍_) ⦃ Path-sub-of-reflexive ⦄

instance
  type-extensionalityₗ-preserves-refl : Preserving₀(_≍_)(Path) (type-extensionality $ₗ_) (reflexivity(_≍_)) (reflexivity(Path) {x = T})
  type-extensionalityₗ-preserves-refl {T = T} = intro \i j → primGlue(T) {i = Interval.max i (Interval.farBound j)}
    (\_ → T)
    (\_ → reflexivity(_≍_))

instance
  type-extensionalityᵣ-preserves-refl : Preserving₀(Path)(_≍_) (type-extensionality $ᵣ_) (reflexivity(Path)) (reflexivity(_≍_) {x = T})
  type-extensionalityᵣ-preserves-refl {T = T} = intro(injective(sub₂(_≍_)(_↔_)) (\i → intro(Interval.transp(\_ → T) i) (Interval.transp(\_ → T) i)))

-- Also called: Univalence axiom for paths
Path-[≍]-path : Path(Path A B) (Lvl.Up(A ≍ B))
Path-[≍]-path{A = A}{B = B} = type-extensionality $ₗ [≍]-transitivity-raw
  (Path-isomorphisms(_≍_) type-extensionality)
  ([≍]-symmetry-raw LvlUp-id-isomorphism)

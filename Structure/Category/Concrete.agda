import      Data.Tuple as Tuple
import      Data.Tuple.Proofs
open        Tuple using (_,_)

  -- The opposite/dual category of a category.
  opposite : Category {Obj} (_⟵_)
  opposite = ?
  {-opposite = record{
      _∘_ = Functional.swap _∘_ ; -- \{x}{y}{z} yz xy → _∘_ {z}{y}{x} xy yz
      id = id ;

      identityₗ = identityᵣ ;
      identityᵣ = identityₗ ;
      associativity = \{x}{y}{z}{w} {f}{g}{h} → symmetry(_≡_) (associativity {w}{z}{y}{x} {h}{g}{f})
    }
-}

  -- The empty category is a category containing nothing.
  -- The objects are empty.
  -- The morphisms are empty.
  emptyCategory : Category{Empty}(empty)
  Category._∘_           (emptyCategory) {}
  Category.id            (emptyCategory) {}
  Category.identityₗ     (emptyCategory) {}
  Category.identityᵣ     (emptyCategory) {}
  Category.associativity (emptyCategory) {}

  -- The single category is a category containing a single object.
  -- The objects consists of a single thing.
  -- The morphisms consists of a single connection connecting the single thing to itself.
  singleCategory : Category{Unit}(const(const Unit))
  Category._∘_           (singleCategory) <> <> = <>
  Category.id            (singleCategory) = <>
  Category.identityₗ     (singleCategory) = reflexivity
  Category.identityᵣ     (singleCategory) = reflexivity
  Category.associativity (singleCategory) = reflexivity

module _ {ℓ} where
  open import Relator.Equals
  open import Relator.Equals.Proofs

  -- open Sets.Setoid{ℓ}

  -- The set category is a category containing all sets/types of a single level in the language.
  -- The objects are all sets/types.
  -- The morphisms are all functions where the domain/codomain-pair are from these objects.
  setCategory : Category{_}{_}{Set(ℓ)}(_→ᶠ_)
  Category._∘_           (setCategory) = _∘f_
  Category.id            (setCategory) = idf
  Category.identityₗ     (setCategory) = reflexivity
  Category.identityᵣ     (setCategory) = reflexivity
  Category.associativity (setCategory) = reflexivity


{- TODO: May have to use an alternative equality definition for the proofs to work? When are two instances of Category equal?

Can some of this be used:
• https://en.wikipedia.org/wiki/Isomorphism_of_categories
• https://en.wikipedia.org/wiki/Equivalence_of_categories
?

module _  where
  open Relator.Equals

  categoryCategory : ∀{ℓₒ ℓₘ}{Obj}{_⟶_} → Category{_}{_} {Category{ℓₒ}{ℓₘ} {Obj} (_⟶_)} (Functor)
  Category._∘_           (categoryCategory) = compositionFunctor
  Category.id            (categoryCategory) {cat} = identityFunctor (cat)
  Category.identityₗ     (categoryCategory) = [≡]-intro
  Category.identityᵣ     (categoryCategory) = [≡]-intro
  Category.associativity (categoryCategory) = [≡]-intro
-}

module _ {ℓ} where
  open import Structure.Operator.Monoid

  monoidCategory : ∀{T : Set(ℓ)}{_▫_ : T → T → T} → Monoid(_▫_) → Category{Obj = Unit}(const(const(T)))
  Category._∘_           (monoidCategory{_}{_▫_}(M)) {_}{_}{_} = (_▫_)
  Category.id            (monoidCategory{_}{_▫_}(M)) {_} = Monoid.id(M)
  Category.identityₗ     (monoidCategory{_}{_▫_}(M)) {_}{_} = Monoid.identityₗ(M)
  Category.identityᵣ     (monoidCategory{_}{_▫_}(M)) {_}{_} = Monoid.identityᵣ(M)
  Category.associativity (monoidCategory{_}{_▫_}(M)) {_}{_}{_}{_} = Monoid.associativity(M)

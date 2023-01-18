{-# OPTIONS --cubical #-}

module Type.Cubical.Path.Equality where

open import Function
open import Function.Equiv as Function
open import Logic.Propositional
import      Lvl
open import Type
open import Type.Cubical
open import Type.Cubical.Path
open import Type.Cubical.Path.Functions as Path
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Setoid using (Equiv ; intro ; _≡_)
open import Structure.Type.Identity
open import Syntax.Function
open import Type.Identity

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₚ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable f g : A → B
private variable _▫_ : A → B → C
private variable P : T → Type{ℓ}
private variable x y : T

instance
  Path-reflexivity : Reflexivity{T = T}(Path)
  Path-reflexivity = intro Path.point

instance
  Path-symmetry : Symmetry{T = T}(Path)
  Path-symmetry = intro Path.reverse

instance
  Path-transitivity : Transitivity{T = T}(Path)
  Path-transitivity = intro Path.concat

instance
  Path-equivalence : Equivalence{T = T}(Path)
  Path-equivalence = intro

instance
  Path-equiv : Equiv(T)
  Path-equiv = intro(Path) ⦃ Path-equivalence ⦄

instance
  Path-congruence₁ : Function(f)
  Path-congruence₁ {f = f} = intro(Path.map f)

instance
  Path-congruence₂ : BinaryOperator(_▫_)
  Path-congruence₂ {_▫_ = _▫_} = intro(Path.map₂(_▫_))

instance
  Path-substitution₁ : UnaryRelator(P)
  Path-substitution₁ {P = P} = intro(Path.liftedSpaceBimap P)

instance
  Path-substitution₂ : BinaryRelator(_▫_)
  Path-substitution₂ {_▫_ = _▫_} = intro(Path.liftedSpaceBimap₂(_▫_))

instance
  Path-coercion : Path ⊆₂ (_→ᶠ_ {ℓ}{ℓ})
  Path-coercion = intro(Path.spaceMap)

-- Path is the smallest reflexive relation.
Path-sub-of-reflexive : ⦃ refl : Reflexivity(_▫_) ⦄ → (Path ⊆₂ (_▫_))
Path-sub-of-reflexive {_▫_ = _▫_} = intro(\{a b} → ab ↦ sub₂(Path)(_→ᶠ_) ⦃ Path-coercion ⦄ (congruence₂-₂(_▫_)(a) ab) (reflexivity(_▫_) {a}))

Path-general-congruence₁ : ⦃ equiv : Equiv{ℓₑ₂}(B) ⦄ → Function ⦃ Path-equiv ⦄ ⦃ equiv ⦄ (f)
Path-general-congruence₁ {f = f} = intro \xy → sub₂(Path)(_≡_) ⦃ Path-sub-of-reflexive ⦄ (congruence₁(f) xy)

Path-general-congruence₂ : ⦃ equiv : Equiv{ℓₑ₃}(C) ⦄ → BinaryOperator ⦃ Path-equiv ⦄ ⦃ Path-equiv ⦄ ⦃ equiv ⦄ (_▫_)
Path-general-congruence₂ {_▫_ = _▫_} = intro \xy₁ xy₂ → sub₂(Path)(_≡_) ⦃ Path-sub-of-reflexive ⦄ (congruence₂(_▫_) xy₁ xy₂)

instance
  Path-function-extensionality : Function.Extensionality Path-equiv (Path-equiv{T = A → B})
  Path-function-extensionality = intro([↔]-intro Path.mappingPoint Path.mapping)

instance
  Path-identity-eliminator : IdentityEliminator(Path{P = T}) {ℓₚ}
  IdentityEliminator.elim Path-identity-eliminator P prefl eq  = sub₂(Path)(_→ᶠ_) ⦃ Path-coercion ⦄ (\i → P(\j → eq(Interval.min i j))) prefl

-- Path is a subrelation of Id.
-- By introducing the cubical primitives, the proofs using Path is able to be transported over to Id. Note for example that this also makes univalence and function extensionality provable for Id.
Path-Id-sub : Path ⊆₂ Id{T = T}
Path-Id-sub = intro \{x} xy → sub₂(Path)(_→ᶠ_) (\i → Id x (xy i)) Id.intro

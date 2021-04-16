{-# OPTIONS --cubical #-}

module Type.Cubical.Path.Equality where

open import Functional
open import Function.Axioms
import      Lvl
open import Type
open import Type.Cubical
open import Type.Cubical.Path
open import Type.Cubical.Path.Proofs as Path
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
open import Structure.Relator.Properties
open import Structure.Relator
open import Structure.Setoid using (Equiv ; intro)
open import Structure.Type.Identity

private variable ℓ ℓ₁ ℓ₂ ℓₚ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable f : A → B
private variable _▫_ : A → B → C
private variable P : T → Type{ℓ}
private variable x y : T

_≡_ : T → T → Type
_≡_ = Path

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
  Path-substitution₁ {P = P} = intro(Path.liftedSpaceMap P)

instance
  Path-substitution₂ : BinaryRelator(_▫_)
  Path-substitution₂ {_▫_ = _▫_} = intro(Path.liftedSpaceMap₂(_▫_))

instance
  Path-coercion : Path ⊆₂ (_→ᶠ_ {ℓ}{ℓ})
  Path-coercion = intro(Path.spaceMap)

Path-sub-of-reflexive : ⦃ refl : Reflexivity(_▫_) ⦄ → (Path ⊆₂ (_▫_))
Path-sub-of-reflexive {_▫_ = _▫_} = intro(\{a b} → ab ↦ sub₂(Path)(_→ᶠ_) ⦃ Path-coercion ⦄ (congruence₂ᵣ(_▫_)(a) ab) (reflexivity(_▫_) {a}))

instance
  Path-function-extensionality : FunctionExtensionality A B
  Path-function-extensionality = intro Path.mapping

instance
  Path-dependent-function-extensionality : ∀{A : Type{ℓ₁}}{B : (a : A) → Type{ℓ₂}} → DependentFunctionExtensionality A B
  Path-dependent-function-extensionality = intro Path.mapping

instance
  Path-function-application : FunctionApplication A B
  Path-function-application = intro Path.mappingPoint

Path-identity-eliminator : IdentityEliminator{ℓₚ = ℓₚ}(Path{P = T})
IdentityEliminator.elim Path-identity-eliminator P prefl eq  = sub₂(Path)(_→ᶠ_) ⦃ Path-coercion ⦄ (\i → P(\j → eq(Interval.min i j))) prefl

-- TODO: Organize and move everything below

open import Type.Properties.MereProposition
open import Type.Properties.Singleton

prop-is-prop-unit : ⦃ proof : MereProposition(A) ⦄ → IsUnit(MereProposition(A))
MereProposition.uniqueness (IsUnit.unit prop-is-prop-unit) {x} {y} = uniqueness _
MereProposition.uniqueness (IsUnit.uniqueness (prop-is-prop-unit {A = A}) {intro p} i) {x}{y} j = Interval.hComp d x where
  d : Interval → Interval.Partial (Interval.max (Interval.max (Interval.flip i) i) (Interval.max (Interval.flip j) j)) A
  d k (i = Interval.𝟎) = uniqueness(A) {x}{p{x}{y} j} k
  d k (i = Interval.𝟏) = uniqueness(A) {x}{uniqueness(A) {x}{y} j} k
  d k (j = Interval.𝟎) = uniqueness(A) {x}{x} k
  d k (j = Interval.𝟏) = uniqueness(A) {x}{y} k

{-
Path-isUnit : ∀{ℓ}{A : Type{ℓ}} → ⦃ _ : MereProposition(A) ⦄ → (∀{x y : A} → IsUnit(x ≡ y))
IsUnit.unit       (Path-isUnit {A = A}) = uniqueness(A)
IsUnit.uniqueness (Path-isUnit {A = A} ⦃ mere-A ⦄ {x = x} {y = y}) {p} i = Interval.hComp d p where
  d : Interval → Interval.Partial (Interval.max (Interval.flip i) i) (Path x y)
  d j (i = Interval.𝟎) = p
  d j (i = Interval.𝟏) = {!uniqueness(A) {x}{y}!}
-- congruence₁ (prop ↦ MereProposition.uniqueness prop {x}{y}) (IsUnit.uniqueness prop-is-prop-unit {intro (\{x y} → {!p!})})
-}

{-
open import Structure.Setoid.Uniqueness
open import Type.Dependent
-}

-- TODO
-- ∀{eu₁ eu₂ : ∃!{Obj = Obj}(Pred)} → () → (eu₁ ≡ eu₂)

{-
Unique-MereProposition-equivalence : ⦃ prop : ∀{x} → MereProposition(P(x)) ⦄ → (Unique(P) ↔ MereProposition(∃ P))
Unique-MereProposition-equivalence {P = P} = [↔]-intro l r where
  l : Unique(P) ← MereProposition(∃ P)
  l (intro p) {x} {y} px py = mapP([∃]-witness) (p{[∃]-intro x ⦃ px ⦄} {[∃]-intro y ⦃ py ⦄})
  r : Unique(P) → MereProposition(∃ P)
  MereProposition.uniqueness (r p) {[∃]-intro w₁ ⦃ p₁ ⦄} {[∃]-intro w₂ ⦃ p₂ ⦄} i = mapP (mapP (\w p → [∃]-intro w ⦃ p ⦄) (p p₁ p₂) i) {!!} i
  -- mapP [∃]-intro (p p₁ p₂) i ⦃ {!!} ⦄

Unique-prop : ⦃ prop : ∀{x} → MereProposition(P(x)) ⦄ → MereProposition(Unique(P))
MereProposition.uniqueness Unique-prop {u₁} {u₂} i {x} {y} px py j = Interval.hComp d x where
  d : Interval → Interval.Partial (Interval.max (Interval.max (Interval.flip i) i) (Interval.max (Interval.flip j) j)) A
  d k (i = Interval.𝟎) = {!!}
  d k (i = Interval.𝟏) = {!!}
  d k (j = Interval.𝟎) = {!!}
  d k (j = Interval.𝟏) = {!!}

[∃!trunc]-to-existence : ⦃ prop : ∀{x} → MereProposition(Pred(x)) ⦄ → HTrunc₁(∃!{Obj = Obj}(Pred)) → HomotopyLevel(0)(∃{Obj = Obj}(Pred))
[∃!trunc]-to-existence {Pred = Pred} (trunc ([∧]-intro e u)) = intro e (\{e₂} i → [∃]-intro (u ([∃]-proof e₂) ([∃]-proof e) i) ⦃ {!!} ⦄)
-- MereProposition.uniqueness test) {u _ _ _}
-- sub₂(_≡_)(_→ᶠ_) ⦃ [≡][→]-sub ⦄ (congruence₁(Pred) ?) ?
[∃!trunc]-to-existence (trunc-proof i) = {!!}
-}

{-
[∃!]-squashed-witness : HTrunc₁(∃!{Obj = Obj}(Pred)) → Obj
[∃!]-squashed-witness (trunc eu) = [∃]-witness([∧]-elimₗ eu)
[∃!]-squashed-witness (trunc-proof {trunc ([∧]-intro e₁ u₁)} {trunc ([∧]-intro e₂ u₂)} i) = u₁ ([∃]-proof e₁) ([∃]-proof e₂) i
[∃!]-squashed-witness (trunc-proof {trunc ([∧]-intro e₁ u₁)} {trunc-proof j} i) = {!!}
[∃!]-squashed-witness (trunc-proof {trunc-proof i₁} {trunc x} i) = {!!}
[∃!]-squashed-witness (trunc-proof {trunc-proof i₁} {trunc-proof i₂} i) = {!!}
-}

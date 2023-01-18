{-# OPTIONS --cubical #-}

module Type.Cubical.Path.Proofs where

open import BidirectionalFunction using (_↔_ ; _$ᵣ_)
import      Lvl
open import Type
open import Type.Cubical
open import Type.Cubical.Path
open import Type.Cubical.Path.Functions
open import Type.Cubical.Path.Equality
open import Type.Properties.MereProposition
open import Type.Properties.Singleton

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}

instance
  prop-is-prop : MereProposition(MereProposition(A))
  MereProposition.uniqueness prop-is-prop {intro prop₁}{intro prop₂} = map intro \i {x}{y} j → Interval.hComp(\k →
    \{
      (i = Interval.𝟎) → prop₁{x}{prop₁{x}{y} j} k ;
      (i = Interval.𝟏) → prop₁{x}{prop₂{x}{y} j} k ;
      (j = Interval.𝟎) → prop₁{x}{x} k ;
      (j = Interval.𝟏) → prop₁{x}{y} k
    })
    x

module _ where
  private variable X : Interval → Type{ℓ}
  private variable Y : (i : Interval) → X(i) → Type{ℓ}

  interval-predicate₀-pathP : ⦃ prop : ∀{i} → MereProposition(X(i)) ⦄ → ∀{x₀ : X(Interval.𝟎)}{x₁ : X(Interval.𝟏)} → PathP X x₀ x₁
  interval-predicate₀-pathP{X = X} = pathPathP(X) $ᵣ uniqueness(X(Interval.𝟏))

  interval-predicate₁-pathP : ⦃ prop : ∀{i : Interval}{x : X(i)} → MereProposition(Y i x) ⦄ → ∀{x₀ : X Interval.𝟎}{x₁ : X Interval.𝟏}{y₀ : Y Interval.𝟎 x₀}{y₁ : Y Interval.𝟏 x₁} → (p : PathP X x₀ x₁) → PathP(\i → Y i (p i)) y₀ y₁
  interval-predicate₁-pathP{Y = Y} p = interval-predicate₀-pathP{X = \i → Y i (p i)}

module _ where
  private variable X : Type{ℓ}
  private variable Y : X → Type{ℓ}

  -- There is a path between all proofs of a predicate when it is a mere proposition and there is a path between the objects.
  interval-predicate₁-path : ⦃ prop : ∀{x : X} → MereProposition(Y(x)) ⦄ → ∀{a₁ b₁ : X}{a₂ : Y(a₁)}{b₂ : Y(b₁)} → (p : Path a₁ b₁) → PathP(\i → Y(p i)) a₂ b₂
  interval-predicate₁-path{X = X}{Y = Y} = interval-predicate₁-pathP{X = \_ → X}{Y = \_ → Y}
  -- NOTE: Alternative proof of interval-predicate₁-path
  -- module _ (P : T → Type{ℓ}) ⦃ prop-P : ∀{c} → MereProposition(P(c)) ⦄ where
  --   property-pathP : ∀{x y}{px : P(x)}{py : P(y)} → (xy : x ≡ y) → PathP(\i → P(xy i)) px py
  --   property-pathP {x}{y}{px}{py} xy = idElim(Path) (xy ↦ (∀{px}{py} → PathP(\i → P(xy i)) px py)) (\{c} → uniqueness(P(c))) {x}{y} xy {px}{py}


{- TODO: Organize and move everything below

open import Type.Properties.MereProposition
open import Type.Properties.Singleton

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
open import Type.Dependent.Sigma
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
-}

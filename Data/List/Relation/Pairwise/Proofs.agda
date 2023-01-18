module Data.List.Relation.Pairwise.Proofs where

open import Data using (<>)
open import Data.List
import      Data.List.Functions as List
open import Data.List.Relation.Pairwise
open import Data.List.Relation.Sublist
open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Universal.Functions
open import Data.List.Relation.Quantification.Universal.Proofs
open import Data.Option.Quantifiers
import      Data.Tuple as Tuple
open import Functional
open import Logic
open import Logic.Propositional
open import Logic.Propositional.Equiv
import      Lvl
open import Structure.Relator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Function
open import Type

private variable ℓ ℓₗ ℓₑ : Lvl.Level
private variable T A B : Type{ℓ}
private variable x y : T
private variable l l₁ l₂ : List(T)
private variable f g : A → B
private variable _▫_ : T → T → Type{ℓₗ}
private variable _▫₁_ : A → A → Type{ℓₗ}
private variable _▫₂_ : B → B → Type{ℓₗ}

----------------------------------------------------------------------------
-- Basic

AdjacentlyPairwise-prepend-min : (∀{y} → (x ▫ y)) → ∀{l} → AdjacentlyPairwise(_▫_)(l) → AdjacentlyPairwise(_▫_)(x ⊰ l)
AdjacentlyPairwise-prepend-min xy {∅}     p = AdjacentlyPairwise.single
AdjacentlyPairwise-prepend-min xy {_ ⊰ _} p = AdjacentlyPairwise.step xy p

AdjacentlyPairwise-head : AdjacentlyPairwise(_▫_)(x ⊰ l) → ∀ₒₚₜ(List.first l) (x ▫_)
AdjacentlyPairwise-head single     = <>
AdjacentlyPairwise-head (step p _) = p

AdjacentlyPairwise-tail : AdjacentlyPairwise(_▫_)(x ⊰ l) → AdjacentlyPairwise(_▫_)(l)
AdjacentlyPairwise-tail single = empty
AdjacentlyPairwise-tail (step _ rest) = rest

OrderedPairwise-head : OrderedPairwise(_▫_)(x ⊰ l) → AllElements(x ▫_)(l)
OrderedPairwise-head (step p _) = p

OrderedPairwise-tail : OrderedPairwise(_▫_)(x ⊰ l) → OrderedPairwise(_▫_)(l)
OrderedPairwise-tail (step _ rest) = rest

OrderedPairwise₌-head : OrderedPairwise₌(_▫_)(x ⊰ l) → AllElements(x ▫_)(x ⊰ l)
OrderedPairwise₌-head (step p _) = p

OrderedPairwise₌-tail : OrderedPairwise₌(_▫_)(x ⊰ l) → OrderedPairwise₌(_▫_)(l)
OrderedPairwise₌-tail (step _ rest) = rest

Pairwise-tail : Pairwise(_▫_)(x ⊰ l) → Pairwise(_▫_)(l)
Pairwise-tail (_ ⊰ ap) = AllElements-fn AllElements-prepend-tail ap

-- TODO: Maybe remove this and prove implication of the first arg with below
AdjacentlyPairwise-prepend : AllElements(x ▫_)(l) → AdjacentlyPairwise(_▫_)(l) → AdjacentlyPairwise(_▫_)(x ⊰ l)
AdjacentlyPairwise-prepend {l = ∅}     _   _      = single
AdjacentlyPairwise-prepend {l = _ ⊰ _} all sorted = step (AllElements-prepend-head all) sorted

AdjacentlyPairwise-prepend-first : ∀ₒₚₜ(List.first l) (x ▫_) → AdjacentlyPairwise(_▫_)(l) → AdjacentlyPairwise(_▫_)(x ⊰ l)
AdjacentlyPairwise-prepend-first {l = ∅}     _ _      = single
AdjacentlyPairwise-prepend-first {l = _ ⊰ _} p sorted = step p sorted

----------------------------------------------------------------------------
-- Applying other functions

AdjacentlyPairwise-map : (∀{x y} → (f(x) ▫₁ f(y)) → (g(x) ▫₂ g(y))) → ∀{l} → AdjacentlyPairwise(_▫₁_)(List.map f l) → AdjacentlyPairwise(_▫₂_)(List.map g(l))
AdjacentlyPairwise-map p {∅} s = AdjacentlyPairwise.empty
AdjacentlyPairwise-map p {x ⊰ ∅} s = AdjacentlyPairwise.single
AdjacentlyPairwise-map p {x ⊰ y ⊰ l} (AdjacentlyPairwise.step s₁ s₂) = AdjacentlyPairwise.step (p s₁) (AdjacentlyPairwise-map p {y ⊰ l} s₂)

OrderedPairwise₌-map : (∀{x y} → (f(x) ▫₁ f(y)) → (g(x) ▫₂ g(y))) → ∀{l} → OrderedPairwise₌(_▫₁_)(List.map f(l)) → OrderedPairwise₌(_▫₂_)(List.map g(l))
OrderedPairwise₌-map                p {∅}    empty      = empty
OrderedPairwise₌-map {f = f}{g = g} p {_ ⊰ _}(step a s) = step (AllElements-map f g p a) (OrderedPairwise₌-map p s)

OrderedPairwise-map : (∀{x y} → (f(x) ▫₁ f(y)) → (g(x) ▫₂ g(y))) → ∀{l} → OrderedPairwise(_▫₁_)(List.map f(l)) → OrderedPairwise(_▫₂_)(List.map g(l))
OrderedPairwise-map                p {∅}     empty      = empty
OrderedPairwise-map {f = f}{g = g} p {_ ⊰ _} (step a s) = step (AllElements-map f g p a) (OrderedPairwise-map p s)

{-
Pairwise-map : (∀{x y} → (x ▫₁ y) → (f(x) ▫₂ f(y))) → ∀{l} → Pairwise(_▫₁_)(l) → Pairwise(_▫₂_)(List.map f(l))
Pairwise-map         p ∅ = ∅
Pairwise-map {f = f} p (head ⊰ rest) = (AllElements-map id f p head) ⊰ {! (AllElements-fn AllElements-prepend-tail rest)!}
-}

AdjacentlyPairwise-[++] : ∀{_▫_ : T → T → Type{ℓ}}{l₁ l₂} → AdjacentlyPairwise(_▫_)(l₁ List.++ l₂) ↔ ((∀ₒₚₜ(List.last l₁) \x₁ → ∀ₒₚₜ(List.first l₂) \x₂ → x₁ ▫ x₂) ∧ AdjacentlyPairwise(_▫_)(l₁) ∧ AdjacentlyPairwise(_▫_)(l₂))
AdjacentlyPairwise-[++] {_▫_ = _▫_} = [↔]-intro (Tuple.uncurry(Tuple.uncurry L)) R where
  L : ∀{l₁ l₂} → (∀ₒₚₜ(List.last l₁) \x₁ → ∀ₒₚₜ(List.first l₂) \x₂ → x₁ ▫ x₂) → AdjacentlyPairwise(_▫_)(l₁) → AdjacentlyPairwise(_▫_)(l₂) → AdjacentlyPairwise(_▫_)(l₁ List.++ l₂)
  L po empty       p2 = p2
  L po single      p2 = AdjacentlyPairwise-prepend-first po p2
  L po (step p p1) p2 = AdjacentlyPairwise-prepend-first p (L po p1 p2)

  R : ∀{l₁ l₂} → AdjacentlyPairwise(_▫_)(l₁ List.++ l₂) → ((∀ₒₚₜ(List.last l₁) \x₁ → ∀ₒₚₜ(List.first l₂) \x₂ → x₁ ▫ x₂) ∧ AdjacentlyPairwise(_▫_)(l₁) ∧ AdjacentlyPairwise(_▫_)(l₂))
  R {∅}          pa          = [∧]-intro ([∧]-intro <> AdjacentlyPairwise.empty) pa
  R {x ⊰ ∅}      single      = [∧]-intro ([∧]-intro <> single) AdjacentlyPairwise.empty
  R {x ⊰ ∅}      (step p pa) = [∧]-intro ([∧]-intro p single) pa
  R {x ⊰ y ⊰ l₁} (step p pa) =
    let [∧]-intro ([∧]-intro a b) c = R {y ⊰ l₁} pa
    in [∧]-intro ([∧]-intro a (AdjacentlyPairwise-prepend-first p b)) c

OrderedPairwise-[++] : ∀{_▫_ : T → T → Type{ℓ}}{l₁ l₂} → OrderedPairwise(_▫_)(l₁ List.++ l₂) ↔ ((∀ₗᵢₛₜ(l₁) \x₁ → ∀ₗᵢₛₜ(l₂) \x₂ → x₁ ▫ x₂) ∧ OrderedPairwise(_▫_)(l₁) ∧ OrderedPairwise(_▫_)(l₂))
OrderedPairwise-[++] {_▫_ = _▫_} = [↔]-intro (Tuple.uncurry(Tuple.uncurry L)) R where
  L : ∀{l₁ l₂} → (∀ₗᵢₛₜ(l₁) \x₁ → ∀ₗᵢₛₜ(l₂) \x₂ → x₁ ▫ x₂) → OrderedPairwise(_▫_)(l₁) → OrderedPairwise(_▫_)(l₂) → OrderedPairwise(_▫_)(l₁ List.++ l₂)
  L po        empty       p2 = p2
  L (pa ⊰ po) (step p p1) p2 = step (AllElements-[++] p pa) (L po p1 p2)

  R : ∀{l₁ l₂} → OrderedPairwise(_▫_)(l₁ List.++ l₂) → ((∀ₗᵢₛₜ(l₁) \x₁ → ∀ₗᵢₛₜ(l₂) \x₂ → x₁ ▫ x₂) ∧ OrderedPairwise(_▫_)(l₁) ∧ OrderedPairwise(_▫_)(l₂))
  R {∅}     {_}  pa          = [∧]-intro ([∧]-intro ∅ empty) pa
  R {x ⊰ l₁}{l₂} (step p pa) =
    let
      [∧]-intro ([∧]-intro a b) c = R {l₁} pa
      [∧]-intro a1 a2 = AllElements-from-[++] {l₁ = l₁}{l₂ = l₂} p
    in [∧]-intro ([∧]-intro (a2 ⊰ a) (step a1 b)) c

----------------------------------------------------------------------------
-- Relation between different "pairwise" relations

import      Structure.Relator.Names as Names
open import Structure.Relator.Properties

instance
  OrderedPairwise-to-AdjacentlyPairwise : OrderedPairwise{ℓ₂ = ℓ}{T = T} ⊆₂ AdjacentlyPairwise
  OrderedPairwise-to-AdjacentlyPairwise = intro p where
    p : Names.Sub₂ OrderedPairwise AdjacentlyPairwise
    p empty          = empty
    p (step all ord) = AdjacentlyPairwise-prepend all (p ord)

instance
  OrderedPairwise₌-to-OrderedPairwise : OrderedPairwise₌{ℓ₂ = ℓ}{T = T} ⊆₂ OrderedPairwise
  OrderedPairwise₌-to-OrderedPairwise = intro p where
    p : Names.Sub₂ OrderedPairwise₌ OrderedPairwise
    p empty = empty
    p (step a rest) = step (AllElements-prepend-tail a) (p rest)

AdjacentlyPairwise-to-OrderedPairwise : ⦃ trans : Transitivity(_▫_) ⦄ → AdjacentlyPairwise(_▫_)(l) → OrderedPairwise(_▫_)(l)
AdjacentlyPairwise-to-OrderedPairwise empty = empty
AdjacentlyPairwise-to-OrderedPairwise single = step ∅ empty
AdjacentlyPairwise-to-OrderedPairwise (step p rest) =
  let next = AdjacentlyPairwise-to-OrderedPairwise rest
  in step (p ⊰ AllElements-of-transitive-binary-relationᵣ p (OrderedPairwise-head next)) next

OrderedPairwise₌-to-reflexivity : OrderedPairwise₌(_▫_)(l) → AllElements((_▫_) $₂_)(l)
OrderedPairwise₌-to-reflexivity empty = ∅
OrderedPairwise₌-to-reflexivity (step (base ⊰ _) rest) = base ⊰ (OrderedPairwise₌-to-reflexivity rest)

Pairwise-symmetric-OrderedPairwise₌-equivalence : Pairwise(_▫_)(l) ↔ OrderedPairwise₌(x ↦ y ↦ (y ▫ x) ∧ (x ▫ y))(l)
Pairwise-symmetric-OrderedPairwise₌-equivalence{_▫_ = _▫_} = [↔]-intro L R where
  R : Pairwise(_▫_)(l) → OrderedPairwise₌(x ↦ y ↦ (y ▫ x) ∧ (x ▫ y))(l)
  R ∅ = empty
  R ((xy ⊰ row) ⊰ rest) = step
    ([∧]-intro xy xy ⊰ [↔]-to-[←] AllElements-[∧]-distributivity ([∧]-intro row (AllElements-prepend-head(AllElements-swap-nested rest))))
    (R (AllElements-fn AllElements-prepend-tail rest))

  L : Pairwise(_▫_)(l) ← OrderedPairwise₌(x ↦ y ↦ (y ▫ x) ∧ (x ▫ y))(l)
  L empty = ∅
  L (step (xa ⊰ a) op) = ([∧]-elimₗ xa ⊰ AllElements-fn [∧]-elimₗ a) ⊰ (AllElements-fn₂ (\xin → [∧]-elimᵣ (AllElements-membership-elim a xin) AllElements.⊰_) AllElements-membership (L op)) where
    open import Relator.Equals.Proofs

instance
  Pairwise-to-OrderedPairwise₌ : Pairwise{ℓ₂ = ℓ}{T = T} ⊆₂ OrderedPairwise₌
  Pairwise-to-OrderedPairwise₌ = intro(OrderedPairwise₌-map{f = id}{g = id} [∧]-elimᵣ ∘ [↔]-to-[→] Pairwise-symmetric-OrderedPairwise₌-equivalence)

OrderedPairwise₌-to-Pairwise : ⦃ sym : Symmetry(_▫_) ⦄ → OrderedPairwise₌(_▫_)(l) → Pairwise(_▫_)(l)
OrderedPairwise₌-to-Pairwise = [↔]-to-[←] Pairwise-symmetric-OrderedPairwise₌-equivalence ∘ OrderedPairwise₌-map{f = id}{g = id} (xy ↦ [∧]-intro (symmetry(_) xy) xy)

OrderedPairwise-to-OrderedPairwise₌ : ⦃ refl : Reflexivity(_▫_) ⦄ → OrderedPairwise(_▫_)(l) → OrderedPairwise₌(_▫_)(l)
OrderedPairwise-to-OrderedPairwise₌ empty = empty
OrderedPairwise-to-OrderedPairwise₌ (step a p) = step (reflexivity(_) ⊰ a) (OrderedPairwise-to-OrderedPairwise₌ p)

----------------------------------------------------------------------------
-- Between different relations

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ rel : BinaryRelator{A = T}(_▫_) ⦄ where
  OrderedPairwise-sublist : (l₁ ⊑ l₂) → (OrderedPairwise(_▫_)(l₁) ← OrderedPairwise(_▫_)(l₂))
  OrderedPairwise-sublist empty empty = empty
  OrderedPairwise-sublist (use xy sub) (step yl₂ pair) = step (AllElements-fn (substitute₂-₁ᵣ(_▫_)(_) (symmetry(_≡_) xy)) (AllElements-sublist ⦃ rel = BinaryRelator.unary₂ _ rel ⦄ sub yl₂)) (OrderedPairwise-sublist sub pair)
  OrderedPairwise-sublist (skip sub) (step xl₂ pair) = OrderedPairwise-sublist sub pair

  {- Note: Unprovable because it is possible for a sublist to skip some of the elements inbetween. Example: AdjacentlyPairwise(_▫_) [a,b,c,d] ⇔ (a ▫ b) ∧ (b ▫ c) ∧ (c ▫ d), and [b,d] ⊑ [a,b,c,d], but (b ▫ d) is not implied. Use Data.List.Relation.Fixes.Infix instead of (_⊑_) and this will be provable because it does not allow skipping any elements
  AdjacentlyPairwise-sublist : (l₁ ⊑ l₂) → (AdjacentlyPairwise(_▫_)(l₁) ← AdjacentlyPairwise(_▫_)(l₂))
  AdjacentlyPairwise-sublist empty empty = empty
  AdjacentlyPairwise-sublist (use x empty) single = single
  AdjacentlyPairwise-sublist (skip empty) single = empty
  AdjacentlyPairwise-sublist (use {l₁ = ∅} x sub) (step p pair) = single
  AdjacentlyPairwise-sublist (use {l₁ = x₁ ⊰ l₁} x (use x₂ sub)) (step p pair) = step (substitute₂ᵣ(_▫_) (symmetry(_≡_) x) (symmetry(_≡_) x₂) p) (AdjacentlyPairwise-sublist (use x₂ sub) pair) -- AdjacentlyPairwise-sublist sub (AdjacentlyPairwise-tail pair)
  AdjacentlyPairwise-sublist (use {l₁ = x₁ ⊰ l₁} x (skip sub)) (step p pair) = step {!(AdjacentlyPairwise-sublist sub (AdjacentlyPairwise-tail pair))!} (AdjacentlyPairwise-sublist sub (AdjacentlyPairwise-tail pair))
  -- step ((substitute₂ₗ(_▫_) (symmetry(_≡_) x)) {!sub!}) (AdjacentlyPairwise-sublist sub pair)
  AdjacentlyPairwise-sublist (skip sub) (step p pair) = AdjacentlyPairwise-sublist sub pair
  -}

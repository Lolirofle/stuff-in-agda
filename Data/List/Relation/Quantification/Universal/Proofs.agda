module Data.List.Relation.Quantification.Universal.Proofs where

import      Lvl
open import Data.List
open import Data.List.Relation.Permutation
open import Data.List.Relation.Quantification
open import Data.List.Relation.Quantification.Universal.Functions
import      Data.Tuple as Tuple
open import Functional
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Logic
open import Structure.Relator.Properties
open import Type

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable l l₁ l₂ : List(T)
private variable ll : List(List(T))
private variable x y : T
private variable P P₁ P₂ Q E : T → Stmt{ℓ}
private variable Q₂ : A → B → Stmt{ℓ}
private variable _▫_ : T → T → Stmt{ℓ}

AllElements-order-independent : ∀{P : T → Type{ℓ}}{l₁ l₂} → (l₁ permutes l₂) → (AllElements P(l₁) → AllElements P(l₂))
AllElements-order-independent _permutes_.empty          ∅           = ∅
AllElements-order-independent (_permutes_.prepend perm) (x ⊰ p)     = x ⊰ AllElements-order-independent perm p
AllElements-order-independent _permutes_.swap           (x ⊰ y ⊰ p) = y ⊰ x ⊰ p
AllElements-order-independent (trans perm₁ perm₂)                   = AllElements-order-independent perm₂ ∘ AllElements-order-independent perm₁

AllElements-of-transitive-binary-relationₗ : ⦃ trans : Transitivity(_▫_) ⦄ → (x ▫ y) → (AllElements (_▫ x) l → AllElements (_▫ y) l)
AllElements-of-transitive-binary-relationₗ             _ ∅        = ∅
AllElements-of-transitive-binary-relationₗ {_▫_ = _▫_} p (a ⊰ al) = transitivity(_▫_) a p ⊰ AllElements-of-transitive-binary-relationₗ p al

AllElements-of-transitive-binary-relationᵣ : ⦃ trans : Transitivity(_▫_) ⦄ → (y ▫ x) → (AllElements (x ▫_) l → AllElements (y ▫_) l)
AllElements-of-transitive-binary-relationᵣ             _ ∅        = ∅
AllElements-of-transitive-binary-relationᵣ {_▫_ = _▫_} p (a ⊰ al) = (transitivity(_▫_) p a) ⊰ AllElements-of-transitive-binary-relationᵣ p al

AllElements-[∃]-proof : ∀{P : T → Type{ℓ}}{l} → AllElements (P ∘ [∃]-witness{Pred = P})(l)
AllElements-[∃]-proof {l = ∅}     = ∅
AllElements-[∃]-proof {l = x ⊰ l} = ([∃]-proof x) ⊰ (AllElements-[∃]-proof {l = l})

AllElements-[∧]-distributivity : AllElements(x ↦ P(x) ∧ Q(x))(l) ↔ (AllElements P(l) ∧ AllElements Q(l))
AllElements-[∧]-distributivity = [↔]-intro L R where
  L : AllElements(x ↦ P(x) ∧ Q(x))(l) ← (AllElements P(l) ∧ AllElements Q(l))
  L (∅ Tuple., ∅) = ∅
  L ([∧]-intro (p ⊰ ap) (q ⊰ aq)) = ([∧]-intro p q) ⊰ L([∧]-intro ap aq)

  R : AllElements(x ↦ P(x) ∧ Q(x))(l) → (AllElements P(l) ∧ AllElements Q(l))
  Tuple.left  (R a) = AllElements-fn [∧]-elimₗ a
  Tuple.right (R a) = AllElements-fn [∧]-elimᵣ a

open import Data.List.Relation.Membership using (_∈_)
open import Structure.Relator
open import Structure.Setoid
module _ {ℓₑ} ⦃ equiv : Equiv{ℓₑ}(T) ⦄ where
  AllElements-membership : AllElements{T = T} (_∈ l)(l)
  AllElements-membership{∅} = ∅
  AllElements-membership{x ⊰ l} = (• reflexivity(_≡_)) ⊰ AllElements-fn ⊰_ (AllElements-membership{l})

  module _ ⦃ rel : UnaryRelator{A = T}(P) ⦄ where
    AllElements-membership-intro : (∀{x} → (x ∈ l) → P(x)) → AllElements P(l)
    AllElements-membership-intro{∅}     p = ∅
    AllElements-membership-intro{x ⊰ l} p = (p{x} (• reflexivity(_≡_))) ⊰ AllElements-membership-intro{l} (p ∘ ⊰_)

    AllElements-membership-elim : AllElements P(l) → (x ∈ l) → P(x)
    AllElements-membership-elim (py ⊰ ap) (• xy) = substitute₁ₗ(P) xy py
    AllElements-membership-elim (py ⊰ ap) (⊰ ex) = AllElements-membership-elim ap ex

    open import Data.List.Relation.Sublist
    AllElements-sublist : (l₁ ⊑ l₂) → (AllElements P(l₁) ← AllElements P(l₂))
    AllElements-sublist empty ∅ = ∅
    AllElements-sublist (use xy sub) (py ⊰ ap) = substitute₁ₗ(P) xy py ⊰ AllElements-sublist sub ap
    AllElements-sublist (_⊑_.skip sub) (_ ⊰ ap) = AllElements-sublist sub ap

-- TODO: Is this actually an algorithm for transposing a list?
AllElements-swap-nested : AllElements(x ↦ AllElements(y ↦ Q₂ x y)(l₁))(l₂) → AllElements(y ↦ AllElements(x ↦ Q₂ x y)(l₂))(l₁)
AllElements-swap-nested ∅ = AllElements-fn (const ∅) ([∀]-to-AllElements ⊤)
AllElements-swap-nested (∅ ⊰ _) = ∅
AllElements-swap-nested ((head ⊰ q₂x) ⊰ tail) =
  let next = AllElements-swap-nested tail
  in (head ⊰ AllElements-prepend-head next) ⊰ AllElements-fn₂ (\yl₁ → (AllElements-membership-elim q₂x yl₁) AllElements.⊰_) AllElements-membership (AllElements-prepend-tail next)
  where open import Relator.Equals.Proofs

module Data.List.Relation.Quantification.Proofs where

import      Lvl
open import Data.List
open import Data.List.Functions
open import Data.List.Proofs.Id
open import Data.List.Relation.Permutation
open import Data.List.Relation.Quantification
open import Functional
open import Logic
open import Structure.Relator.Properties
open import Type

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable l l₁ l₂ : List(T)
private variable ll : List(List(T))
private variable x : T
private variable P Q : T → Stmt{ℓ}
private variable Q₂ : A → B → Stmt{ℓ}
private variable _▫_ : T → T → Stmt{ℓ}

AllElements-map : (f : A → B) → (g : A → C) → (∀{x} → P(f(x)) → Q(g(x))) → (AllElements P(map f(l)) → AllElements Q(map g(l)))
AllElements-map {l = ∅}     f g pq ∅        = ∅
AllElements-map {l = x ⊰ l} f g pq (p ⊰ ap) = pq p ⊰ AllElements-map f g pq ap

AllElements-mapᵣ : (f : A → B) → (∀{x} → P(x) → Q(f(x))) → (AllElements P l → AllElements Q (map f(l)))
AllElements-mapᵣ = AllElements-map id

AllElements-mapₗ : (f : A → B) → (∀{x} → P(f(x)) → Q(x)) → (AllElements P (map f(l)) → AllElements Q l)
AllElements-mapₗ f = AllElements-map f id

AllElements-fn : (∀{x} → P(x) → Q(x)) → (AllElements P l → AllElements Q l)
AllElements-fn = AllElements-map id id

AllElements-[++] : AllElements P l₁ → AllElements P l₂ → AllElements P (l₁ ++ l₂)
AllElements-[++] {l₁ = ∅}     p       q = q
AllElements-[++] {l₁ = _ ⊰ _} (x ⊰ p) q = x ⊰ AllElements-[++] p q

AllElements-concat : (AllElements (AllElements P) l → AllElements P (concat l))
AllElements-concat ∅        = ∅
AllElements-concat (p ⊰ pl) = AllElements-[++] p (AllElements-concat pl)

AllElements-concatMap : (f : A → List(B)) → (∀{x} → P(x) → AllElements Q(f(x))) → (AllElements P(l) → AllElements Q(concatMap f(l)))
AllElements-concatMap f pq ∅       = ∅
AllElements-concatMap f pq (x ⊰ p) = AllElements-[++] (pq x) (AllElements-concatMap f pq p)

AllElements-order-independent : ∀{P : T → Type{ℓ}}{l₁ l₂} → (l₁ permutes l₂) → (AllElements P(l₁) → AllElements P(l₂))
AllElements-order-independent _permutes_.empty          ∅           = ∅
AllElements-order-independent (_permutes_.prepend perm) (x ⊰ p)     = x ⊰ AllElements-order-independent perm p
AllElements-order-independent _permutes_.swap           (x ⊰ y ⊰ p) = y ⊰ x ⊰ p
AllElements-order-independent (trans perm₁ perm₂)                   = AllElements-order-independent perm₂ ∘ AllElements-order-independent perm₁

AllElements-of-transitive-binary-relationₗ : ⦃ trans : Transitivity(_▫_) ⦄ → (l₁ ▫ l₂) → (AllElements (_▫ l₁) ll → AllElements (_▫ l₂) ll)
AllElements-of-transitive-binary-relationₗ             _ ∅        = ∅
AllElements-of-transitive-binary-relationₗ {_▫_ = _▫_} p (a ⊰ al) = transitivity(_▫_) a p ⊰ AllElements-of-transitive-binary-relationₗ p al

AllElements-of-transitive-binary-relationᵣ : ⦃ trans : Transitivity(_▫_) ⦄ → (l₂ ▫ l₁) → (AllElements (l₁ ▫_) ll → AllElements (l₂ ▫_) ll)
AllElements-of-transitive-binary-relationᵣ             _ ∅        = ∅
AllElements-of-transitive-binary-relationᵣ {_▫_ = _▫_} p (a ⊰ al) = (transitivity(_▫_) p a) ⊰ AllElements-of-transitive-binary-relationᵣ p al

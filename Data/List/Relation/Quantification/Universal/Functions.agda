module Data.List.Relation.Quantification.Universal.Functions where

import      Lvl
import      Data.Option.Functions as Option
open import Data.List
open import Data.List.Functions
open import Data.List.Equiv.Id
open import Data.List.Relation.Quantification
open import Functional
open import Logic.Propositional
open import Logic
open import Type.Dependent.Sigma
open import Type

private variable ℓ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable l l₁ l₂ : List(T)
private variable ll : List(List(T))
private variable x y : T
private variable P P₁ P₂ Q E : T → Stmt{ℓ}
private variable Q₂ : A → B → Stmt{ℓ}
private variable _▫_ : T → T → Stmt{ℓ}

AllElements-prepend-head : AllElements P(x ⊰ l) → P(x)
AllElements-prepend-head (px ⊰ _) = px

AllElements-prepend-tail : AllElements P(x ⊰ l) → AllElements P(l)
AllElements-prepend-tail (_ ⊰ pl) = pl

AllElements-tail : AllElements P(l) → AllElements P(tail l)
AllElements-tail ∅        = ∅
AllElements-tail (_ ⊰ pl) = pl

AllElements-map : (f : A → B) → (g : A → C) → (∀{x} → P(f(x)) → Q(g(x))) → (AllElements P(map f(l)) → AllElements Q(map g(l)))
AllElements-map {l = ∅}     f g pq ∅        = ∅
AllElements-map {l = x ⊰ l} f g pq (p ⊰ ap) = pq p ⊰ AllElements-map f g pq ap

AllElements-mapᵣ : (f : A → B) → (∀{x} → P(x) → Q(f(x))) → (AllElements P l → AllElements Q (map f(l)))
AllElements-mapᵣ = AllElements-map id

AllElements-mapₗ : (f : A → B) → (∀{x} → P(f(x)) → Q(x)) → (AllElements P (map f(l)) → AllElements Q l)
AllElements-mapₗ f = AllElements-map f id

AllElements-fn : (∀{x} → P(x) → Q(x)) → (AllElements P l → AllElements Q l)
AllElements-fn = AllElements-map id id

AllElements-head-tail : AllElements P(l) ↔ (Option.partialMap ⊤ P(first l) ∧ AllElements P(tail l))
AllElements-head-tail = [↔]-intro L R where
  L : AllElements P(l) ← (Option.partialMap ⊤ P(first l) ∧ AllElements P(tail l))
  L {l = ∅}     ([∧]-intro h t) = t
  L {l = x ⊰ l} ([∧]-intro h t) = h ⊰ t

  R : AllElements P(l) → (Option.partialMap ⊤ P(first l) ∧ AllElements P(tail l))
  R ∅         = [∧]-intro [⊤]-intro ∅
  R (px ⊰ ap) = [∧]-intro px ap

{-
import      Data.List.FunctionsProven as Proven
AllElements-proven-map : (f : (x : A) → E(x) → B) → (g : (x : A) → E(x) → C) → (∀{x} → (px : E(x)) → P(f x px) → Q(g x px)) → (e : AllElements E(l)) → (AllElements P(Proven.map f l e) → AllElements Q(Proven.map g l e))
AllElements-proven-map {l = ∅}     f g pq ∅        ∅        = ∅
AllElements-proven-map {l = x ⊰ l} f g pq (e ⊰ ae) (p ⊰ ap) = pq e p ⊰ AllElements-proven-map f g pq ae ap

open import Data.List.FunctionsProven.Proofs
AllElements-fn₂ : (∀{x} → (px : E(x)) → P(x) → Q(x)) → AllElements E(l) → (AllElements P l → AllElements Q l)
AllElements-fn₂{l = l} = {!Proven.map Dependent.const l ([∀]-to-AllElements ⊤)!} -- AllElements-proven-map const const
-}

AllElements-[++] : AllElements P l₁ → AllElements P l₂ → AllElements P (l₁ ++ l₂)
AllElements-[++] {l₁ = ∅}     p       q = q
AllElements-[++] {l₁ = _ ⊰ _} (x ⊰ p) q = x ⊰ AllElements-[++] p q

AllElements-from-[++] : AllElements P (l₁ ++ l₂) → (AllElements P l₁ ∧ AllElements P l₂)
AllElements-from-[++] {l₁ = ∅}     ap       = [∧]-intro ∅ ap
AllElements-from-[++] {l₁ = x ⊰ l} (p ⊰ ap) =
  let [∧]-intro p1 p2 = AllElements-from-[++] {l₁ = l} ap
  in [∧]-intro (p ⊰ p1) p2

AllElements-concat : (AllElements (AllElements P) l → AllElements P (concat l))
AllElements-concat ∅        = ∅
AllElements-concat (p ⊰ pl) = AllElements-[++] p (AllElements-concat pl)

AllElements-concatMap : (f : A → List(B)) → (∀{x} → P(x) → AllElements Q(f(x))) → (AllElements P(l) → AllElements Q(concatMap f(l)))
AllElements-concatMap f pq ∅       = ∅
AllElements-concatMap f pq (x ⊰ p) = AllElements-[++] (pq x) (AllElements-concatMap f pq p)

AllElements-sigma : Σ(List(T)) (AllElements(P)) ↔ List(Σ T P)
AllElements-sigma = [↔]-intro L R where
  L : Σ(List(T)) (AllElements(P)) ← List(Σ T P)
  L ∅                 = intro ∅ ∅
  L ((intro x p) ⊰ sl) =
    let (intro l pl) = L sl
    in  intro (x ⊰ l) (p ⊰ pl)

  R : Σ(List(T)) (AllElements(P)) → List(Σ T P)
  R (intro ∅       ∅)        = ∅
  R (intro (x ⊰ l) (p ⊰ pl)) = intro x p ⊰ R(intro l pl)

foldᵣ-property-all : ∀{ℓ₁ ℓ₂ ℓₗ₁ ℓₗ₂}{A : Type{ℓ₁}}{B : Type{ℓ₂}}{P : A → Type{ℓₗ₁}}{Q : B → Type{ℓₗ₂}}{_▫_}{id} → ((∀{a b} → P(a) → Q(b) → Q(a ▫ b)) → Q(id) → ∀{l} → AllElements P(l) → Q(foldᵣ(_▫_) id l))
foldᵣ-property-all                _   pid {∅}     _        = pid
foldᵣ-property-all {P = P}{Q = Q} pop pid {x ⊰ l} (p ⊰ ap) = pop p (foldᵣ-property-all {P = P}{Q = Q} pop pid {l} ap)

AllElements-fn₂ : (∀{x} → P₁(x) → P₂(x) → Q(x)) → AllElements P₁(l) → AllElements P₂(l) → AllElements Q(l)
AllElements-fn₂ pqr ∅        ∅        = ∅
AllElements-fn₂ pqr (p ⊰ ap) (q ⊰ aq) = pqr p q ⊰ AllElements-fn₂ pqr ap aq

[∀]-to-AllElements : (∀{x} → P(x)) → AllElements P(l)
[∀]-to-AllElements {l = ∅}     p = ∅
[∀]-to-AllElements {l = x ⊰ l} p = p ⊰ [∀]-to-AllElements p

AllElements-postpend : P(x) → AllElements P(l) → AllElements P(postpend x l)
AllElements-postpend {l = ∅} px apl = px ⊰ apl
AllElements-postpend {l = prepend x l} px (py ⊰ apl) = py ⊰ (AllElements-postpend px apl)

module Data.List.Relation.Quantification.Existential.Proofs where

import Lvl
open import Functional
open import Function.Names
open import Function.EqualsRaw
open import Data.Boolean
open import Data.Boolean.Stmt
import      Data.Either as Either
open import Data.List
open import Data.List.Functions hiding (skip)
open import Data.List.Relation.Membership
open import Data.List.Relation.Quantification
open import Logic.Propositional
open import Logic.Propositional.Equiv
open import Structure.Function
import      Structure.Function.Names as Names
open import Structure.Relator
import      Structure.Relator.Names as Names
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑₗ : Lvl.Level
private variable T A B C : Type{ℓ}

module _  where
  private variable l l₁ l₂ : List(T)
  private variable ll : List(List(T))
  private variable a b c x : T
  private variable f : A → B
  private variable P Q : T → Type{ℓ}

  private variable ℓ₁ ℓ₂ : Lvl.Level

  ExistsElement-empty : ¬ ExistsElement P(∅)
  ExistsElement-empty ()

  instance
    ExistsElement-compatibleₗ : Compatible₁(Names.Sub₁)(_→ᶠ_) (swap(ExistsElement{ℓ = ℓ}) l)
    ExistsElement-compatibleₗ = intro proof where
      proof : Names.Compatible₁(\A B → (∀{x} → A(x) → B(x)))(_→ᶠ_)(swap(ExistsElement{ℓ = ℓ}) l)
      proof pq (• px) = • pq px
      proof pq (⊰ ep) = ⊰ proof pq ep

  instance
    ExistsElement-relatorₗ : UnaryRelator(swap(ExistsElement{ℓ = ℓ}) l)
    ExistsElement-relatorₗ = UnaryRelator-introᵣ proof where
      proof : Names.Substitution₁ᵣ(swap ExistsElement l)
      proof pq (• px) = • [↔]-to-[→] pq px
      proof pq (⊰ ep) = ⊰ proof pq ep

  ExistsElement-singleton : ExistsElement P(singleton(a)) ↔ P(a)
  ExistsElement-singleton = [↔]-intro (•_) (\{(use p) → p})

  ExistsElement-[++] : ExistsElement P(l₁ ++ l₂) ↔ (ExistsElement P(l₁) ∨ ExistsElement P(l₂))
  ExistsElement-[++] = [↔]-intro L R where
    L : ExistsElement P(l₁ ++ l₂) ← (ExistsElement P(l₁) ∨ ExistsElement P(l₂))
    L {l₁ = ∅}      ([∨]-introᵣ p)     = p
    L {l₁ = x ⊰ l₁} ([∨]-introₗ (• p)) = • p
    L {l₁ = x ⊰ l₁} ([∨]-introₗ (⊰ p)) = ⊰ L {l₁ = l₁} ([∨]-introₗ p)
    L {l₁ = x ⊰ l₁} ([∨]-introᵣ p)     = ⊰ L {l₁ = l₁} ([∨]-introᵣ p)

    R : ExistsElement P(l₁ ++ l₂) → (ExistsElement P(l₁) ∨ ExistsElement P(l₂))
    R {l₁ = ∅}      p     = [∨]-introᵣ p
    R {l₁ = x ⊰ l₁} (• p) = [∨]-introₗ (• p)
    R {l₁ = x ⊰ l₁} (⊰ p) with R {l₁ = l₁} p
    ... | [∨]-introₗ q = [∨]-introₗ (⊰ q)
    ... | [∨]-introᵣ q = [∨]-introᵣ q

  ExistsElement-prepend : ExistsElement P(prepend a l) ↔ (P(a) ∨ ExistsElement P(l))
  ExistsElement-prepend = [↔]-intro
    ([∨]-elim (•_) (⊰_))
    (\{(• px) → [∨]-introₗ px ; (⊰ ep) → [∨]-introᵣ ep})

  ExistsElement-postpend : ExistsElement P(postpend a l) ↔ (ExistsElement P(l) ∨ P(a))
  ExistsElement-postpend = [↔]-intro L R where
    L : ExistsElement P(postpend a l) ← (ExistsElement P(l) ∨ P(a))
    L{l = ∅}     ([∨]-introₗ ())
    L{l = x ⊰ l} ([∨]-introₗ (• px)) = • px
    L{l = x ⊰ l} ([∨]-introₗ (⊰ ep)) = ⊰ L{l = l} ([∨]-introₗ ep)
    L{l = ∅}     ([∨]-introᵣ p) = • p
    L{l = x ⊰ l} ([∨]-introᵣ p) = ⊰ L{l = l} ([∨]-introᵣ p)

    R : ExistsElement P(postpend a l) → (ExistsElement P(l) ∨ P(a))
    R {l = ∅}     (• px) = [∨]-introᵣ px
    R {l = x ⊰ l} (• px) = [∨]-introₗ (• px)
    R {l = x ⊰ l} (⊰ ep) = Either.mapLeft ⊰_ (R {l = l} ep)

  open import Data
  open import Data.Boolean.Stmt.Logic
  open import Lang.Inspect
  open import Type.Identity.Proofs

  ExistsElement-filter : ∀{f} → ExistsElement P(filter f(l)) ↔ ExistsElement(x ↦ P(x) ∧ IsTrue(f(x)))(l)
  ExistsElement-filter{l = ll}{f = f} = [↔]-intro L R where
    L : ExistsElement P(filter f(l)) ← ExistsElement(x ↦ P(x) ∧ IsTrue(f(x)))(l)
    L (•_ {x} ([∧]-intro px fx)) with 𝑇 ← f(x) = • px
    L (⊰_ {_}{x} epf) with f(x)
    L (⊰_ epf) | 𝑇 = ⊰ L epf
    L (⊰_ epf) | 𝐹 = L epf

    R : ExistsElement P(filter f(l)) → ExistsElement(x ↦ P(x) ∧ IsTrue(f(x)))(l)
    R {l = x ⊰ l} e with f(x) | inspect ⦃ Id-equiv ⦄ f(x)
    R {l = x ⊰ l} (• px) | 𝑇 | intro fx = • [∧]-intro px ([↔]-to-[←] IsTrue.is-𝑇 fx)
    R {l = x ⊰ l} (⊰ e)  | 𝑇 | intro fx = ⊰ R{l = l} e
    R {l = x ⊰ l} e      | 𝐹 | intro fx = ⊰ R{l = l} e

  ExistsElement-map : ExistsElement P(map f(l)) ↔ ExistsElement(P ∘ f)(l)
  ExistsElement-map = [↔]-intro L R where
    L : ExistsElement P(map f(l)) ← ExistsElement(P ∘ f)(l)
    L(• pfx) = • pfx
    L(⊰ epf) = ⊰ L epf

    R : ExistsElement P(map f(l)) → ExistsElement(P ∘ f)(l)
    R {l = _ ⊰ _} (• pfx) = • pfx
    R {l = _ ⊰ l} (⊰ ep)  = ⊰ R{l = l} ep

  ExistsElement-concat : ExistsElement P(concat ll) ↔ ExistsElement(ExistsElement P)(ll)
  ExistsElement-concat = [↔]-intro L R where
    L : ExistsElement P(concat ll) ← ExistsElement(ExistsElement P)(ll)
    L {ll = l ⊰ ll} (• ep)  = [↔]-to-[←] (ExistsElement-[++] {l₁ = l}{l₂ = concat ll}) ([∨]-introₗ ep)
    L {ll = l ⊰ ll} (⊰ eep) = [↔]-to-[←] (ExistsElement-[++] {l₁ = l}{l₂ = concat ll}) ([∨]-introᵣ (L{ll = ll} eep))

    R : ExistsElement P(concat ll) → ExistsElement(ExistsElement P)(ll)
    R {ll = l ⊰ ll} ep = [∨]-elim
      (•_)
      (⊰_ ∘ R{ll = ll})
      ([↔]-to-[→] (ExistsElement-[++] {l₁ = l}{l₂ = concat ll}) ep)

  module _ where
    open import Data.List.Equiv.Id
    open import Relator.Equals
    open import Relator.Equals.Proofs.Equiv
    open import Syntax.Implication

    ExistsElement-concatMap : ExistsElement P(concatMap f(l)) ↔ ExistsElement((ExistsElement P) ∘ f)(l)
    ExistsElement-concatMap{P = P}{f = f}{l = l} =
      ExistsElement P(concatMap f l)           ⇔-[ substitute₁(ExistsElement P) (concatMap-concat-map{f = f}{l}) ]
      ExistsElement P(concat(map f(l)))        ⇔-[ ExistsElement-concat ]
      ExistsElement(ExistsElement P)(map f(l)) ⇔-[ ExistsElement-map ]
      ExistsElement((ExistsElement P) ∘ f) l   ⇔-end

open import Data.List.Equiv
open import Structure.Relator.Properties
open import Structure.Setoid renaming (_≡_ to _≡ₛ_)

module _
  ⦃ equiv : Equiv{ℓₑ}(T) ⦄
  ⦃ equiv-List : Equiv{ℓₑₗ}(List(T)) ⦄
  ⦃ ext : Extensionality(equiv-List) ⦄
  where

  private variable P Q : T → Type{ℓ}

  instance
    ExistsElement-relatorᵣ : ⦃ UnaryRelator(P) ⦄ → UnaryRelator(ExistsElement P)
    ExistsElement-relatorᵣ{P = P} = UnaryRelator-introᵣ proof where
      proof : Names.Substitution₁ᵣ(ExistsElement P)
      proof {∅}     {l₂}     l₁l₂ ()
      proof {x ⊰ l₁}{∅}      l₁l₂ with () ← [∅][⊰]-unequal (symmetry(_≡ₛ_) l₁l₂)
      proof {x ⊰ l₁}{y ⊰ l₂} l₁l₂ (• px) = • substitute₁ᵣ(P) ([⊰]-generalized-cancellationᵣ l₁l₂) px
      proof {x ⊰ l₁}{y ⊰ l₂} l₁l₂ (⊰ ep) = ⊰ proof{l₁}{l₂} ([⊰]-generalized-cancellationₗ l₁l₂) ep

  open import Data.List.Relation.Permutation
  open import Data.List.Relation.Permutation.Proofs
  instance
    ExistsElement-relatorᵣ-by-permutation : UnaryRelator ⦃ permutes-equiv ⦄ (ExistsElement P)
    ExistsElement-relatorᵣ-by-permutation = UnaryRelator-introᵣ ⦃ permutes-equiv ⦄ p where
      p : Names.Substitution₁ᵣ ⦃ permutes-equiv ⦄ (ExistsElement P)
      p (_permutes_.prepend perm) (• px)     = • px
      p (_permutes_.prepend perm) (⊰ ep)     = ⊰ p perm ep
      p _permutes_.swap           (• px)     = ⊰ (• px)
      p _permutes_.swap           (⊰ (• px)) = • px
      p _permutes_.swap           (⊰ (⊰ ep)) = ⊰ (⊰ ep)
      p (trans perm₁ perm₂)       ep         = p perm₂ (p perm₁ ep)

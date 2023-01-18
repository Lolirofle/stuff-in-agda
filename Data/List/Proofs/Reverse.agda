module Data.List.Proofs.Reverse where

import Lvl
import      Functional as Fn
open import Data.List
open import Data.List.Equiv
open import Data.List.Functions
open import Data.List.Proofs
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Multi
import      Structure.Function.Names as Names
open import Structure.Operator.Properties
open import Structure.Operator
open import Structure.Relator.Properties
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓₑ ℓₑₗ ℓₑₒ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑₗ₁ ℓₑₗ₂ ℓₑₗ₃ : Lvl.Level
private variable T A B C D : Type{ℓ}

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ equiv-List : Equiv{ℓₑₗ}(List(T)) ⦄ ⦃ extensionality : Extensionality(equiv-List) ⦄ where
  private variable l l₁ l₂ : List(T)
  private variable a : T

  instance
    reverse-preserves-prepend-postpend : Preserving₁(reverse)(prepend a)(postpend a)
    reverse-preserves-prepend-postpend{a = a} = intro \{l} →
      reverse(a ⊰ l)                             🝖[ _≡_ ]-[]
      foldₗ(Fn.swap(_⊰_)) (singleton a) l        🝖[ _≡_ ]-[ foldₗ-[⊱]-move-to-end{lₑ = singleton a}{l = l} ]
      (foldₗ(Fn.swap(_⊰_)) ∅ l) ++ (singleton a) 🝖[ _≡_ ]-[ postpend-[++] ]-sym
      postpend a (foldₗ(Fn.swap(_⊰_)) ∅ l)       🝖[ _≡_ ]-[]
      postpend a (reverse l)                     🝖-end

  instance
    reverse-function : Function(reverse)
    reverse-function = intro p where
      p : Names.Congruence₁(reverse)
      p {∅}      {∅}      pl = reflexivity(_≡_)
      p {∅}      {y ⊰ yl} pl with () ← [∅][⊰]-unequal pl
      p {x ⊰ xl} {∅}      pl with () ← [∅][⊰]-unequal (symmetry(_≡_) pl)
      p {x ⊰ xl} {y ⊰ yl} pl =
        reverse(x ⊰ xl)         🝖[ _≡_ ]-[ preserving₁(reverse)(prepend x)(postpend x) {xl} ]
        postpend x (reverse xl) 🝖[ _≡_ ]-[ congruence₂(postpend) ([⊰]-generalized-cancellationᵣ pl) (p([⊰]-generalized-cancellationₗ pl)) ]
        postpend y (reverse yl) 🝖[ _≡_ ]-[ preserving₁(reverse)(prepend y)(postpend y) {yl} ]-sym
        reverse(y ⊰ yl)         🝖-end

  instance
    reverse-preserves-postpend-prepend : Preserving₁(reverse)(postpend a)(prepend a)
    reverse-preserves-postpend-prepend{a = a} = intro \{l} → p{l} where
      p : (reverse(postpend a l) ≡ a ⊰ reverse l)
      p {∅}     = reflexivity(_≡_)
      p {x ⊰ l} =
        reverse(postpend a (x ⊰ l))        🝖[ _≡_ ]-[]
        reverse(x ⊰ postpend a l)          🝖[ _≡_ ]-[ preserving₁(reverse)(prepend x)(postpend x) {postpend a l} ]
        postpend x (reverse(postpend a l)) 🝖[ _≡_ ]-[ congruence₂-₂(postpend)(x) {reverse(postpend a l)}{a ⊰ reverse l} (p{l}) ]
        a ⊰ postpend x (reverse l)         🝖[ _≡_ ]-[ congruence₂-₂(_⊰_)(a) (preserving₁(reverse)(prepend x)(postpend x) {l}) ]-sym
        a ⊰ reverse(x ⊰ l)                 🝖-end

  instance
    reverse-preserves-[++] : Preserving₂(reverse)(_++_)(Fn.swap(_++_))
    reverse-preserves-[++] = intro \{l₁}{l₂} → p{l₁}{l₂} where
      p : reverse(l₁ ++ l₂) ≡ reverse(l₂) ++ reverse(l₁)
      p {l₁ = ∅} {l₂ = l₂} =
        reverse(∅ ++ l₂)        🝖[ _≡_ ]-[]
        reverse l₂              🝖[ _≡_ ]-[ identityᵣ(_++_)(∅) ]-sym
        reverse l₂ ++ ∅         🝖[ _≡_ ]-[]
        reverse l₂ ++ reverse ∅ 🝖-end
      p {l₁ = x ⊰ l₁} {l₂ = l₂} =
        reverse((x ⊰ l₁) ++ l₂)                 🝖[ _≡_ ]-[]
        reverse(x ⊰ (l₁ ++ l₂))                 🝖[ _≡_ ]-[ preserving₁(reverse)(prepend x)(postpend x) {l₁ ++ l₂} ]
        postpend x (reverse(l₁ ++ l₂))          🝖[ _≡_ ]-[ congruence₂-₂(postpend)(x) (p {l₁ = l₁} {l₂ = l₂}) ]
        postpend x (reverse(l₂) ++ reverse(l₁)) 🝖[ _≡_ ]-[ postpend-of-[++] {l₁ = reverse l₂} {l₂ = reverse l₁} ]
        reverse l₂ ++ postpend x (reverse(l₁))  🝖[ _≡_ ]-[ congruence₂-₂(_++_)(reverse l₂) (preserving₁(reverse)(prepend x)(postpend x) {l₁}) ]-sym
        reverse l₂ ++ reverse(x ⊰ l₁)           🝖-end

  instance
    reverse-involution : Involution(reverse{T = T})
    reverse-involution = intro proof where
      proof : Names.Involution(reverse{T = T})
      proof {x = ∅}     = reflexivity(_≡_)
      proof {x = x ⊰ l} =
        reverse(reverse(x ⊰ l))         🝖[ _≡_ ]-[ congruence₁(reverse) (preserving₁(reverse)(prepend x)(postpend x) {l}) ]
        reverse(postpend x (reverse l)) 🝖[ _≡_ ]-[ preserving₁(reverse)(postpend x)(prepend x) {reverse l} ]
        x ⊰ reverse(reverse l)          🝖[ _≡_ ]-[ congruence₂-₂(_⊰_)(x) (proof{x = l}) ]
        x ⊰ l                           🝖-end

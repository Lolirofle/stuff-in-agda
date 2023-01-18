module Data.List.Relation.Permutation.ByInsertion.Proofs where

open import Data.List as List hiding (elim ; prepend)
open import Data.List.Functions as List using (length ; insertIn)
open import Data.List.Proofs.Length
open import Data.List.Relation.Permutation.ByInsertion
import      Lvl
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Structure.Function
open import Syntax.Transitivity
open import Type

private variable ℓ : Lvl.Level
private variable T : Type{ℓ}
private variable x : T
private variable l₁ l₂ : List(T)
private variable perm perm₁ perm₂ : l₁ permutes l₂

permutes-preserves-length : (l₁ permutes l₂) → (length(l₁) ≡ length(l₂))
permutes-preserves-length empty = [≡]-intro
permutes-preserves-length (ins{l₁ = l₁}{l₂ = l₂}{x = x} n p) =
  length(insertIn x l₁ n) 🝖[ _≡_ ]-[ length-insertIn{l = l₁}{n = n} ]
  𝐒(length(l₁))           🝖[ _≡_ ]-[ congruence₁(𝐒) (permutes-preserves-length p) ]
  𝐒(length(l₂))           🝖[ _≡_ ]-[]
  length(x ⊰ l₂)          🝖-end

{-prop : (perm₁ perm₂ : l₁ permutes l₂) → (perm₁ ≡ perm₂)
prop = elim(\{l₁}{l₂} perm₁ → (perm₂ : l₁ permutes l₂) → (perm₁ ≡ perm₂))
  (\{empty → [≡]-intro})
  \{l₁}{l₂}{x}{n} perm₁ prev → {!elim(\{l₁}{l₂} perm₂ → ∀{n} → (perm₁ : l₁ permutes l₂) → (perm₁ ≡ perm₂)) ? ?!}-}
{-prop {l₁ = ∅} {∅} empty empty = {!!}
prop {l₁ = ∅} {x ⊰ l₂} perm₁ perm₂ = {!perm₁ perm₂!}
prop {l₁ = x ⊰ l₁} {x₁ ⊰ l₂} perm₁ perm₂ = {!perm₁ perm₂!}-}

{-
open import Data
open import Data.Option
import      Data.Option.Functions as Option
import      Data.Option.Relation as Option
open import Data.Tuple
open import Numeral.Finite
open import Type.Dependent.Sigma

permutesPrev : ∀{l₁ l₂ : List(T)} → (l₁ permutes l₂) → Option(T ⨯ Σ(List(T) ⨯ List(T)) (\(l₁ , l₂) → 𝕟₌(length l₁) ⨯ (l₁ permutes l₂)))
permutesPrev empty = None
permutesPrev (ins{l₁}{l₂}{x} i perm) = Some(x , intro(l₁ , l₂) (i , perm))

instance
  permutesPrev-of-prepend : ∀{p : l₁ permutes (x ⊰ l₂)} → Option.IsSome(permutesPrev(p))
  permutesPrev-of-prepend {p = ins n p} = <>

-- permutesPrev-inverse : ∀{perm : l₁ permutes (x ⊰ l₂)} → (Option.extract(permutesPrev perm))

permutesPrev-injective : (permutesPrev perm₁ ≡ permutesPrev perm₂) → (perm₁ ≡ perm₂)
permutesPrev-injective {_} {_} {.∅} {∅} {empty} {empty} x = [≡]-intro
permutesPrev-injective {_} {_} {.(insertIn x₁ _ n)} {x₁ ⊰ l₂} {ins n perm₁} {perm₂} eq = {!!}

prop : (perm₁ perm₂ : l₁ permutes l₂) → (perm₁ ≡ perm₂)
prop {l₂ = ∅} empty empty = [≡]-intro
prop {l₂ = y ⊰ l₂} perm₁ perm₂ =
  let perm₁Prev = Option.extract(permutesPrev perm₁)
      perm₂Prev = Option.extract(permutesPrev perm₂)
  in {!!}
-}

module Data.List.Relation.Fixes where

import      Lvl
open import Data.List
open import Logic
open import Logic.Propositional
open import Structure.Setoid
open import Type

private variable ℓ ℓₑ ℓₑ₁ ℓₑ₂ : Lvl.Level
private variable T : Type{ℓ}
private variable x y : T
private variable l fix : List(T)

module _ ⦃ equiv : Equiv{ℓₑ₁}(T) ⦄ where
  -- `Prefix l fix` states that `fix` is a prefix in `l`.
  -- `fix` is a part of `l` that includes the beginning.
  -- Example (All prefixes of [0,1,2]):
  --   Prefix [0,1,2] []
  --   Prefix [0,1,2] [0]
  --   Prefix [0,1,2] [0,1]
  --   Prefix [0,1,2] [0,1,2]
  -- Alternative definition:
  --   Prefix l fix = (∃ \rest → l ≡ (fix ++ rest))
  data Prefix : List(T) → List(T) → Type{Lvl.of(T) Lvl.⊔ ℓₑ₁} where
    empty : Prefix l ∅
    use   : (x ≡ y) → Prefix l fix → Prefix (x ⊰ l) (y ⊰ fix)

  -- `Infix l fix` states that `fix` is an infix in `l`.
  -- `fix` is a part of `l`.
  -- Example (All infixes of [0,1,2]):
  --   Infix [0,1,2] []
  --   Infix [0,1,2] [0]
  --   Infix [0,1,2] [1]
  --   Infix [0,1,2] [2]
  --   Infix [0,1,2] [0,1]
  --   Infix [0,1,2] [1,2]
  --   Infix [0,1,2] [0,1,2]
  -- Alternative definition:
  --   Infix l fix = (∃ \start → ∃ \end → l ≡ (start ++ fix ++ end))
  data Infix : List(T) → List(T) → Type{Lvl.of(T) Lvl.⊔ ℓₑ₁} where
    skip  : Infix l fix → Infix (x ⊰ l) fix
    use   : Prefix l fix → Infix l fix

module _ ⦃ equiv : Equiv{ℓₑ₁}(T) ⦄ ⦃ equiv-list : Equiv{ℓₑ₂}(List(T)) ⦄ where
  -- `Suffix l fix` states that `fix` is a suffix in `l`.
  -- `fix` is a part of `l` that includes the end.
  -- Example (All suffixes of [0,1,2]):
  --   Suffix [0,1,2] []
  --   Suffix [0,1,2] [2]
  --   Suffix [0,1,2] [1,2]
  --   Suffix [0,1,2] [0,1,2]
  -- Alternative definition:
  --   Suffix l fix = (∃ \rest → l ≡ (rest ++ fix))
  data Suffix : List(T) → List(T) → Type{Lvl.of(T) Lvl.⊔ ℓₑ₁ Lvl.⊔ ℓₑ₂} where
    empty : Suffix ∅ ∅
    skip  : Suffix l fix → Suffix (x ⊰ l) fix
    use   : (x ≡ y) → (l ≡ fix) → Suffix (x ⊰ l) (y ⊰ fix)



module _ ⦃ equiv : Equiv{ℓₑ₁}(T) ⦄ where
  open import Data.List.Functions using (tail)
  open import Structure.Relator.Properties
  import      Structure.Relator.Names as Names

  private variable l₁ l₂ : List(T)

  Prefix-tail : Prefix l₁ l₂ → Prefix (tail l₁) (tail l₂)
  Prefix-tail {∅}      {∅}      p         = p
  Prefix-tail {x ⊰ l₁} {∅}      p         = empty
  Prefix-tail {x ⊰ l₁} {y ⊰ l₂} (use _ p) = p

  instance
    Prefix-Infix-sub : Prefix ⊆₂ Infix
    Prefix-Infix-sub = intro use

  open import Data.List.Equiv

  module _ ⦃ equiv-list : Equiv{ℓₑ₂}(List(T)) ⦄ ⦃ ext : Extensionality(equiv-list) ⦄ where
    instance
      [≡]-Prefix-sub : (_≡_) ⊆₂ Prefix
      [≡]-Prefix-sub = intro p where
        p : Names.Subrelation (_≡_) Prefix
        p {∅}      {∅}      eq = empty
        p {∅}      {y ⊰ l₂} eq with () ← [∅][⊰]-unequal eq
        p {x ⊰ l₁} {∅}      eq with () ← [∅][⊰]-unequal (symmetry(_≡_) eq)
        p {x ⊰ l₁} {y ⊰ l₂} eq = use ([⊰]-generalized-cancellationᵣ eq) (p([⊰]-generalized-cancellationₗ eq))

    instance
      [≡]-Suffix-sub : (_≡_) ⊆₂ Suffix
      [≡]-Suffix-sub = intro p where
        p : Names.Subrelation (_≡_) Suffix
        p {∅}      {∅}      eq = empty
        p {∅}      {y ⊰ l₂} eq with () ← [∅][⊰]-unequal eq
        p {x ⊰ l₁} {∅}      eq with () ← [∅][⊰]-unequal (symmetry(_≡_) eq)
        p {x ⊰ l₁} {y ⊰ l₂} eq = use ([⊰]-generalized-cancellationᵣ eq) ([⊰]-generalized-cancellationₗ eq)

    instance
      Suffix-Infix-sub : Suffix ⊆₂ Infix
      Suffix-Infix-sub = intro p where
        p : Names.Subrelation Suffix Infix
        p {.∅}       {.∅}       empty             = use empty
        p {.(_ ⊰ _)} {l₂}       (Suffix.skip suf) = skip (p suf)
        p {.(_ ⊰ _)} {.(_ ⊰ _)} (use xy lfix)     = use(use xy (sub₂(_≡_)(Prefix) lfix))

    {-
    instance
      [≡]-Infix-sub : (_≡_) ⊆₂ Infix
      [≡]-Infix-sub = {!transitivity(_⊆₂_) ⦃ ? ⦄ ? ?!}
    -}

{- TODO: Move these examples
open import Relator.Equals
open import Relator.Equals.Proofs
open import Numeral.Natural
test : Suffix (1 ⊰ 2 ⊰ 3 ⊰ 4 ⊰ 5 ⊰ ∅) (4 ⊰ 5 ⊰ ∅)
test = skip (skip (skip (use [≡]-intro [≡]-intro)))

test2 : Suffix (1 ⊰ 2 ⊰ 3 ⊰ 4 ⊰ 5 ⊰ ∅) (4 ⊰ ∅)
test2 = skip (skip (skip (use [≡]-intro {!!})))
-}

open import Data.Boolean
import      Data.Boolean.Operators
open        Data.Boolean.Operators.Programming using (_&&_ ; _||_)
open import Data.List.Functions using (satisfiesAll₂)
open import Functional

module _ (_≡?_ : T → T → Bool) where
  -- Whether a list is the beginning of another list.
  isPrefix : List(T) → List(T) → Bool
  isPrefix = satisfiesAll₂(_≡?_) (const(const 𝑇)) (const(const 𝐹))

  -- Whether a list is the middle of another list.
  isInfix : List(T) → List(T) → Bool
  isInfix ∅       ∅       = 𝑇
  isInfix ∅       (_ ⊰ _) = 𝐹
  isInfix (x ⊰ l) fix     with isPrefix (x ⊰ l) fix
  ... | 𝑇 = 𝑇
  ... | 𝐹 = isInfix l fix

  -- Whether a list is the end of another list.
  isSuffix : List(T) → List(T) → Bool
  isSuffix ∅       ∅       = 𝑇
  isSuffix ∅       (_ ⊰ _) = 𝐹
  isSuffix (x ⊰ l) fix with satisfiesAll₂(_≡?_) (const(const 𝐹)) (const(const 𝐹)) (x ⊰ l) fix
  ... | 𝑇 = 𝑇
  ... | 𝐹 = isSuffix l fix

open import Operator.Equals
open import Type.Properties.Decidable

module _ ⦃ equiv : Equiv{ℓₑ}(T) ⦄ ⦃ dec : EquivDecidable(T) ⦄ where
  open import Data.Boolean.Decidable
  open import Data.Boolean.Stmt.Proofs
  open import Lang.Inspect
  open        Operator.Equals
  open import Relator.Equals.Proofs.Equivalence
  open import Type.Properties.Decidable.Proofs

  instance
    Prefix-decidable : Decider(2)(Prefix)(isPrefix(_==_))
    Prefix-decidable {∅}      {∅}      = true empty
    Prefix-decidable {∅}      {x ⊰ y}  = false \()
    Prefix-decidable {x ⊰ l₁} {∅}      = true empty
    Prefix-decidable {x ⊰ l₁} {y ⊰ l₂} with (x == y) | inspect ⦃ [≡]-equiv ⦄ (x ==_) y
    Prefix-decidable {x ⊰ l₁} {y ⊰ l₂} | 𝑇 | intro _  with isPrefix(_==_) l₁ l₂ | Prefix-decidable{l₁}{l₂}
    Prefix-decidable {x ⊰ l₁} {y ⊰ l₂} | 𝑇 | intro xy | 𝑇 | true  p = true(use (([↔]-to-[←] decider-true ∘ [↔]-to-[←] IsTrue.is-𝑇) xy) p)
    Prefix-decidable {x ⊰ l₁} {y ⊰ l₂} | 𝑇 | intro xy | 𝐹 | false p = false(p ∘ Prefix-tail)
    Prefix-decidable {x ⊰ l₁} {y ⊰ l₂} | 𝐹 | intro nxy = false \{(use xy _) → ([↔]-to-[←] decider-false ∘ [↔]-to-[←] IsFalse.is-𝐹) nxy xy}

  instance
    Infix-decidable : Decider(2)(Infix)(isInfix(_==_))
    Infix-decidable {∅}      {∅}      = true(use empty)
    Infix-decidable {∅}      {x ⊰ y}  = false \{(use())}
    Infix-decidable {x ⊰ l₁} {l₂}     with isPrefix(_==_) (x ⊰ l₁) l₂ | inspect ⦃ [≡]-equiv ⦄ (isPrefix(_==_) (x ⊰ l₁)) l₂
    Infix-decidable {x ⊰ l₁} {l₂} | 𝑇 | intro eq = true(use(([↔]-to-[←] (decider-true ⦃ Prefix-decidable ⦄) ∘ [↔]-to-[←] IsTrue.is-𝑇) eq))
    Infix-decidable {x ⊰ l₁} {l₂} | 𝐹 | intro eq with isInfix(_==_) l₁ l₂ | Infix-decidable{l₁}{l₂}
    Infix-decidable {x ⊰ l₁} {l₂} | 𝐹 | intro eq | 𝑇 | true  p  = true (skip p)
    Infix-decidable {x ⊰ l₁} {l₂} | 𝐹 | intro eq | 𝐹 | false np = false \{
      (skip prev) → np prev ;
      (use pre) → ([↔]-to-[←] (decider-false ⦃ Prefix-decidable ⦄) ∘ [↔]-to-[←] IsFalse.is-𝐹) eq pre }

  {- TODO: Consider redefining isSuffix to be more efficient before proving this. The problem is that when satisfiesAll₂ returns 𝐹 because it reached the end of the list, the recursion will still continue, and that is unnecessary
  module _ ⦃ equiv-list : Equiv{ℓₑ₂}(List(T)) ⦄ where
    instance
      Suffix-decidable : Decider(2)(Suffix)(isSuffix(_==_))
      Suffix-decidable {∅}      {∅}      = true empty
      Suffix-decidable {∅}      {x ⊰ y}  = false \()
      Suffix-decidable {x ⊰ l₁} {∅}      = {!!}
      Suffix-decidable {x ⊰ l₁} {y ⊰ l₂} = {!!}
  -}

{- TODO: Move these examples
open import Numeral.Natural.Decidable
open import Type.Properties.Decidable
open import Numeral.Natural.Oper.Comparisons
a = {!isPrefix(_≡?_) (1 ⊰ 2 ⊰ 3 ⊰ 4 ⊰ 5 ⊰ ∅) (2 ⊰ 3 ⊰ 4 ⊰ ∅)!}
b = {!isSuffix(_≡?_) ∅ ∅!}
-}

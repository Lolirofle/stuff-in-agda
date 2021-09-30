module Numeral.Natural.Sequence.Proofs where

import      Lvl
open import Data
open import Data.Either as Either using (_‖_)
open import Data.Either.Equiv as Either
open import Data.Either.Equiv.Id
open import Data.Either.Proofs as Either
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
open import Data.Tuple.Equiv as Tuple
open import Data.Tuple.Equiv.Id
open import Data.Tuple.Proofs as Tuple
open import Functional
open import Function.Proofs
open import Lang.Inspect
open import Logic
open import Logic.Propositional
open import Logic.Predicate
open import Numeral.Natural
open import Numeral.Natural.Oper
open import Numeral.Natural.Oper.DivMod.Proofs
open import Numeral.Natural.Oper.FlooredDivision
open import Numeral.Natural.Oper.FlooredDivision.Proofs.Algorithm
open import Numeral.Natural.Sequence
open import Relator.Equals renaming (_≡_ to Id)
open import Relator.Equals.Proofs.Equiv{T = ℕ}
open import Relator.Equals.Proofs.Equivalence using () renaming ([≡]-equiv to Id-equiv ; [≡]-to-function to Id-to-function)
open import Structure.Function
open import Structure.Function.Domain
open import Structure.Function.Domain.Proofs
import      Structure.Function.Names as Names
open import Structure.Operator
open import Structure.Setoid
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ₄ ℓₑ₅ ℓₑ₆ : Lvl.Level
private variable n : ℕ
private variable A : Type{ℓ}
private variable B : Type{ℓ}

alternate₂-args : ∀{n} → (alternate₂(n ⋅ 2) ≡ Either.Left(n)) ∧ (alternate₂(𝐒(n ⋅ 2)) ≡ Either.Right(n))
alternate₂-args {0}       = [∧]-intro [≡]-intro [≡]-intro
alternate₂-args {1}       = [∧]-intro [≡]-intro [≡]-intro
alternate₂-args {𝐒(𝐒(n))} with [∧]-intro l r ← alternate₂-args {n} rewrite l rewrite r = [∧]-intro [≡]-intro [≡]-intro

alternate₂-values : ∀{n} → (alternate₂(n) ≡ Either.Left(n ⌊/⌋ 2)) ∨ (alternate₂(n) ≡ Either.Right(n ⌊/⌋ 2))
alternate₂-values {0}       = Either.Left  [≡]-intro
alternate₂-values {1}       = Either.Right [≡]-intro
alternate₂-values {𝐒(𝐒(n))}
  rewrite inddiv-result-𝐒 {0}{1}{n}{1}
  with alternate₂-values {n}
... | Either.Left  eq rewrite eq = Either.Left  [≡]-intro
... | Either.Right eq rewrite eq = Either.Right [≡]-intro

instance
  alternate₂-inverseₗ : Inverseₗ(alternate₂)(unalternate₂)
  alternate₂-inverseₗ = intro proof where
    p : ∀{e} → (unalternate₂(Either.map 𝐒 𝐒 e) ≡ 𝐒(𝐒(unalternate₂ e)))
    p {Either.Left  _} = [≡]-intro
    p {Either.Right _} = [≡]-intro

    proof : Names.Inverses(unalternate₂)(alternate₂)
    proof {0}       = [≡]-intro
    proof {1}       = [≡]-intro
    proof {𝐒(𝐒(n))} =
      (unalternate₂ ∘ alternate₂) (𝐒(𝐒(n)))        🝖[ _≡_ ]-[]
      unalternate₂(alternate₂(𝐒(𝐒(n))))            🝖[ _≡_ ]-[]
      unalternate₂(Either.map 𝐒 𝐒 (alternate₂ n)) 🝖[ _≡_ ]-[ p{alternate₂ n} ]
      𝐒(𝐒(unalternate₂(alternate₂ n)))             🝖[ _≡_ ]-[ congruence₁(𝐒) (congruence₁(𝐒) (proof {n})) ]
      𝐒(𝐒(n))                                      🝖-end

instance
  alternate₂-inverseᵣ : Inverseᵣ(alternate₂)(unalternate₂)
  alternate₂-inverseᵣ = intro proof where
    proof : Names.Inverses(alternate₂)(unalternate₂)
    proof {Either.Left  n} = [∧]-elimₗ alternate₂-args
    proof {Either.Right n} = [∧]-elimᵣ alternate₂-args

instance
  alternate₂-inverse : Inverse(alternate₂)(unalternate₂)
  alternate₂-inverse = [∧]-intro alternate₂-inverseₗ alternate₂-inverseᵣ

instance
  alternate₂-bijective : Bijective(alternate₂)
  alternate₂-bijective = invertible-to-bijective ⦃ inver = [∃]-intro unalternate₂ ⦃ [∧]-intro Id-to-function alternate₂-inverse ⦄ ⦄

pairIndexing-def3 : ∀{a b} → (pairIndexing a (𝐒 b) ≡ 𝐒(pairIndexing (𝐒 a) b))
pairIndexing-def3 {𝟎}   {b} = [≡]-intro
pairIndexing-def3 {𝐒 a} {b} = [≡]-intro

instance
  {-# TERMINATING #-}
  pairIndexing-inverseₗ : Inverseₗ(Tuple.uncurry pairIndexing)(diagonalFilling)
  pairIndexing-inverseₗ = intro proof where
    proof : Names.Inverses(diagonalFilling)(Tuple.uncurry pairIndexing)
    proof {𝟎    , 𝟎}    = [≡]-intro
    proof {𝐒(a) , 𝟎}    with diagonalFilling(pairIndexing 𝟎 a) | proof {𝟎 , a}
    ... | 𝟎    , 𝟎    | [≡]-intro = [≡]-intro
    ... | 𝟎    , 𝐒(d) | [≡]-intro = [≡]-intro
    ... | 𝐒(c) , 𝟎    | ()
    ... | 𝐒(c) , 𝐒(d) | ()
    {-# CATCHALL #-}
    proof {a    , 𝐒(b)} rewrite pairIndexing-def3 {a}{b} with diagonalFilling(pairIndexing (𝐒(a)) b) | proof {𝐒(a) , b}
    ... | 𝟎    , 𝟎    | ()
    ... | 𝟎    , 𝐒(d) | ()
    ... | 𝐒(c) , 𝟎    | [≡]-intro = [≡]-intro
    ... | 𝐒(c) , 𝐒(d) | [≡]-intro = [≡]-intro

instance
  pairIndexing-inverseᵣ : Inverseᵣ(Tuple.uncurry pairIndexing)(diagonalFilling)
  pairIndexing-inverseᵣ = intro proof where
    proof : Names.Inverses(Tuple.uncurry pairIndexing)(diagonalFilling)
    proof {𝟎}    = [≡]-intro
    proof {𝐒(n)} with diagonalFilling n | proof {n}
    ... | (𝟎    , b) | q = congruence₁(𝐒) q
    ... | (𝐒(a) , b) | q rewrite pairIndexing-def3 {a}{b} = congruence₁(𝐒) q

instance
  pairIndexing-inverse : Inverse(Tuple.uncurry pairIndexing)(diagonalFilling)
  pairIndexing-inverse = [∧]-intro pairIndexing-inverseₗ pairIndexing-inverseᵣ

instance
  diagonalFilling-inverse : Inverse(diagonalFilling)(Tuple.uncurry pairIndexing)
  diagonalFilling-inverse = [∧]-intro pairIndexing-inverseᵣ pairIndexing-inverseₗ

instance
  pairIndexing-bijective : Bijective(Tuple.uncurry pairIndexing)
  pairIndexing-bijective = invertible-to-bijective ⦃ inver = [∃]-intro diagonalFilling ⦃ [∧]-intro [≡]-function pairIndexing-inverse ⦄ ⦄

instance
  diagonalFilling-bijective : Bijective(diagonalFilling)
  diagonalFilling-bijective = invertible-to-bijective ⦃ inver = [∃]-intro (Tuple.uncurry pairIndexing) ⦃ [∧]-intro Id-to-function diagonalFilling-inverse ⦄ ⦄

tupleIndexing-inverseᵣ : Inverseᵣ(tupleIndexing{𝐒(n)})(spaceFilling{𝐒(n)})
tupleIndexing-inverseᵣ{n} = intro(proof{n}) where
  proof : ∀{n} → Names.Inverses(tupleIndexing{𝐒(n)})(spaceFilling{𝐒(n)})
  proof {𝟎}   {_} = [≡]-intro
  proof {𝐒(n)}{i} with (x , y) ← diagonalFilling i | intro [≡]-intro ← inspect diagonalFilling i =
    pairIndexing x (tupleIndexing{𝐒(n)} (spaceFilling{𝐒(n)} y)) 🝖[ _≡_ ]-[ congruence₁(pairIndexing(x)) (proof{n}{y}) ]
    pairIndexing x y                                            🝖[ _≡_ ]-[ inverseᵣ(Tuple.uncurry pairIndexing)(diagonalFilling) ]
    i                                                           🝖-end

tupleIndexing-inverseₗ : Inverseₗ(tupleIndexing{𝐒(n)})(spaceFilling{𝐒(n)})
tupleIndexing-inverseₗ{n} = intro(proof{n}) where
  proof : ∀{n} → Names.Inverses(spaceFilling{𝐒(n)})(tupleIndexing{𝐒(n)})
  proof {𝟎}   {_}      = [≡]-intro
  proof {𝐒(n)}{x , xs} =
    Tuple.mapRight spaceFilling (diagonalFilling (pairIndexing x (tupleIndexing xs))) 🝖[ _≡_ ]-[ congruence₁(Tuple.mapRight spaceFilling) (inverseₗ(Tuple.uncurry pairIndexing)(diagonalFilling)) ]
    Tuple.mapRight spaceFilling (x , tupleIndexing xs)                                🝖[ _≡_ ]-[]
    (x , spaceFilling(tupleIndexing xs))                                              🝖[ _≡_ ]-[ congruence₂ᵣ(_,_)(x) (proof{n}{xs}) ]
    (x , xs)                                                                          🝖-end

instance
  tupleIndexing-inverse : Inverse(tupleIndexing{𝐒(n)})(spaceFilling{𝐒(n)})
  tupleIndexing-inverse = [∧]-intro tupleIndexing-inverseₗ tupleIndexing-inverseᵣ

instance
  tupleIndexing-bijective : Bijective(tupleIndexing{𝐒(n)})
  tupleIndexing-bijective = invertible-to-bijective ⦃ inver = [∃]-intro spaceFilling ⦃ [∧]-intro [≡]-function tupleIndexing-inverse ⦄ ⦄

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-AB : Equiv{ℓₑ}(A ‖ B) ⦄ ⦃ ext-AB : Either.Extensionality ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ (equiv-AB) ⦄
  {af : ℕ → A} ⦃ bij-af : Bijective ⦃ [≡]-equiv ⦄ ⦃ equiv-A ⦄ (af) ⦄
  {bf : ℕ → B} ⦃ bij-bf : Bijective ⦃ [≡]-equiv ⦄ ⦃ equiv-B ⦄ (bf) ⦄
  where

  instance
    interleave-bijective : Bijective(interleave af bf)
    interleave-bijective = [∘]-bijective ⦃ bij-f = Either.map-bijective ⦄ ⦃ bij-g = alternate₂-bijective ⦄

module _
  ⦃ equiv-A : Equiv{ℓₑ₁}(A) ⦄
  ⦃ equiv-B : Equiv{ℓₑ₂}(B) ⦄
  ⦃ equiv-AB : Equiv{ℓₑ}(A ⨯ B) ⦄ ⦃ ext-AB : Tuple.Extensionality ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ (equiv-AB) ⦄
  {af : ℕ → A} ⦃ bij-af : Bijective ⦃ [≡]-equiv ⦄ ⦃ equiv-A ⦄ (af) ⦄
  {bf : ℕ → B} ⦃ bij-bf : Bijective ⦃ [≡]-equiv ⦄ ⦃ equiv-B ⦄ (bf) ⦄
  where

  instance
    pair-bijective : Bijective ⦃ [≡]-equiv ⦄ ⦃ equiv-AB ⦄ (pair af bf)
    pair-bijective = [∘]-bijective ⦃ bij-f = Tuple.map-bijective ⦃ Id-equiv ⦄ ⦃ Id-equiv ⦄ ⦃ equiv-A ⦄ ⦃ equiv-B ⦄ ⦃ Id-equiv ⦄ ⦄ ⦃ bij-g = diagonalFilling-bijective ⦄







{- TODO: Old stuff. Probably okay to delete? But maybe it could be handy when the new interleave is used (it is similar to the old one)?

-- Interleaves two sequences into one, alternating between the elements from each sequence.
interleave : (ℕ → A) → (ℕ → B) → (ℕ → (A ‖ B))
interleave af bf 𝟎        = Either.Left(af(𝟎))
interleave af bf (𝐒 𝟎)    = Either.Right(bf(𝟎))
interleave af bf (𝐒(𝐒 n)) = interleave (af ∘ 𝐒) (bf ∘ 𝐒) n




private variable af : ℕ → A
private variable bf : ℕ → B

interleave-left : ∀{n} → (interleave af bf (2 ⋅ n) ≡ Either.Left(af(n)))
interleave-left {n = 𝟎}   = [≡]-intro
interleave-left {n = 𝐒 n} = interleave-left {n = n}

interleave-right : ∀{n} → (interleave af bf (𝐒(2 ⋅ n)) ≡ Either.Right(bf(n)))
interleave-right {n = 𝟎}   = [≡]-intro
interleave-right {n = 𝐒 n} = interleave-right {n = n}


interleave-values : ∀{n} → (interleave af bf n ≡ Either.Left(af(n ⌊/⌋ 2))) ∨ (interleave af bf n ≡ Either.Right(bf(n ⌊/⌋ 2)))
interleave-values                    {n = 𝟎}      = [∨]-introₗ [≡]-intro
interleave-values                    {n = 𝐒 𝟎}    = [∨]-introᵣ [≡]-intro
interleave-values {af = af}{bf = bf} {n = 𝐒(𝐒 n)} = interleave-values {af = af ∘ 𝐒}{bf = bf ∘ 𝐒} {n = n}

interleave-left-args : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) ↔ (m ≡ 2 ⋅ n)
interleave-left-args {n = n} = [↔]-intro (\{[≡]-intro → interleave-left{n = n}}) r where
  r : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) → (m ≡ 2 ⋅ n)
  r {af = af} {m = 𝟎}{n = n} = congruence₁(2 ⋅_) ∘ injective(af) ∘ injective(Either.Left) ⦃ Left-injective ⦄
  r {af = af}{bf = bf} {m = 𝐒 (𝐒 m)}{n = 𝟎} p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒 m)}
  ... | [∨]-introₗ v with () ← injective(af) (injective(Either.Left) ⦃ Left-injective ⦄ (symmetry(_≡_) v 🝖 p))
  ... | [∨]-introᵣ v with () ← symmetry(_≡_) v 🝖 p
  r {af = af} {m = 𝐒 (𝐒 m)}{n = 𝐒 n} p = congruence₁(𝐒 ∘ 𝐒) (r ⦃ [∘]-injective {f = af} ⦄{m = m}{n = n} p)

interleave-right-args : ⦃ _ : Injective(bf) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Right(bf(n))) ↔ (m ≡ 𝐒(2 ⋅ n))
interleave-right-args {n = n} = [↔]-intro (\{[≡]-intro → interleave-right{n = n}}) r where
  r : ⦃ _ : Injective(bf) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Right(bf(n))) → (m ≡ 𝐒(2 ⋅ n))
  r {bf = bf} {m = 𝐒 𝟎}{n = n} = congruence₁(𝐒 ∘ (2 ⋅_)) ∘ injective(bf) ∘ injective(Either.Right) ⦃ Right-injective ⦄
  r {bf = bf}{af = af} {m = 𝐒 (𝐒 m)}{n = 𝟎} p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒 m)}
  ... | [∨]-introₗ v with () ← symmetry(_≡_) v 🝖 p
  ... | [∨]-introᵣ v with () ← injective(bf) (injective(Either.Right) ⦃ Right-injective ⦄ (symmetry(_≡_) v 🝖 p))
  r {bf = bf} {m = 𝐒 (𝐒 m)}{n = 𝐒 n} p = congruence₁(𝐒 ∘ 𝐒) (r ⦃ [∘]-injective {f = bf} ⦄{m = m}{n = n} p)

interleave-step-left : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) ↔ (interleave af bf (𝐒(𝐒 m)) ≡ Either.Left(af(𝐒 n)))
interleave-step-left{af = iaf}{bf = ibf}{m = m}{n = n} = [↔]-intro (l{af = iaf}{bf = ibf}{m = m}{n = n}) (r{af = iaf}{bf = ibf}{m = m}{n = n}) where
  l : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) ← (interleave af bf (𝐒(𝐒 m)) ≡ Either.Left(af(𝐒 n)))
  l {af = af}          {m = 𝟎}      {n}   = congruence₁(Either.Left) ∘ congruence₁(af) ∘ injective(𝐒) ∘ injective(af) ∘ injective(Either.Left) ⦃ Left-injective ⦄
  l {af = af}{bf = bf} {m = 𝐒 (𝐒 m)}{𝟎}   p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒(𝐒(𝐒 m)))}
  ... | [∨]-introₗ v with () ← injective(af) (injective(Either.Left) ⦃ Left-injective ⦄ (symmetry(_≡_) v 🝖 p))
  ... | [∨]-introᵣ v with () ← symmetry(_≡_) v 🝖 p
  l {af = af}          {m = 𝐒 (𝐒 m)}{𝐒 n} = l {af = af ∘ 𝐒} ⦃ [∘]-injective {f = af} ⦄ {m = m}{n}

  r : ⦃ _ : Injective(af) ⦄ → ∀{m n} → (interleave af bf m ≡ Either.Left(af(n))) → (interleave af bf (𝐒(𝐒 m)) ≡ Either.Left(af(𝐒 n)))
  r {af = af}          {m = 𝟎}      {n}   = congruence₁(Either.Left) ∘ congruence₁(af) ∘ congruence₁(𝐒) ∘ injective(af) ∘ injective(Either.Left) ⦃ Left-injective ⦄
  r {af = af}{bf = bf} {m = 𝐒(𝐒 m)} {𝟎}   p with interleave-values {af = af}{bf = bf}{n = 𝐒(𝐒 m)}
  ... | [∨]-introₗ v with () ← injective(af) (injective(Either.Left) ⦃ Left-injective ⦄ (symmetry(_≡_) v 🝖 p))
  ... | [∨]-introᵣ v with () ← symmetry(_≡_) v 🝖 p
  r {af = af}          {m = 𝐒(𝐒 m)} {𝐒 n} = r {af = af ∘ 𝐒} ⦃ [∘]-injective {f = af} ⦄ {m = m}{n}


postulate interleave-injective-raw : ⦃ inj-af : Injective(af) ⦄ → ⦃ inj-bf : Injective(bf) ⦄ → Names.Injective(interleave af bf)
{-interleave-injective-raw {af = af} {bf = bf} {x = 𝟎}       {y = 𝟎}       fxfy = [≡]-intro
interleave-injective-raw {af = af} {bf = bf} {x = 𝟎}       {y = 𝐒 (𝐒 y)} fxfy = symmetry(_≡_) ([↔]-to-[→] (interleave-left-args {bf = bf}) (symmetry(_≡_) fxfy))
interleave-injective-raw {af = af} {bf = bf} {x = 𝐒 (𝐒 x)} {y = 𝟎}       fxfy = [↔]-to-[→] (interleave-left-args {bf = bf}) fxfy
interleave-injective-raw {af = af} {bf = bf} {x = 𝐒 𝟎} {y = 𝐒 𝟎} fxfy = [≡]-intro
interleave-injective-raw {af = af} {bf = bf} {x = 𝐒 𝟎} {y = 𝐒 (𝐒 y)} fxfy = symmetry(_≡_) ([↔]-to-[→] (interleave-right-args {bf = bf}{af = af}) (symmetry(_≡_) fxfy))
interleave-injective-raw {af = af} {bf = bf} {x = 𝐒 (𝐒 x)} {y = 𝐒 𝟎} fxfy = [↔]-to-[→] (interleave-right-args {bf = bf}{af = af}) fxfy
interleave-injective-raw {af = af} {bf = bf} {x = 𝐒 (𝐒 x)} {y = 𝐒 (𝐒 y)} fxfy with interleave-values {af = af ∘ 𝐒}{bf = bf ∘ 𝐒}{n = x} | interleave-values {af = af ∘ 𝐒}{bf = bf ∘ 𝐒}{n = y}
... | [∨]-introₗ p | [∨]-introₗ q = {!congruence₁(𝐒) (injective(af) (injective(Either.Left) (symmetry(_≡_) p 🝖 fxfy 🝖 q)))!} -- TODO: interleave-left and a proof of the division algorihm would work here instead of using interleave-values. Or alternatively, use this, multiply by 2, prove the divisibilities for both cases so that each case have division as inverse of multiplication
... | [∨]-introₗ p | [∨]-introᵣ q = {!!}
... | [∨]-introᵣ p | [∨]-introₗ q = {!!}
... | [∨]-introᵣ p | [∨]-introᵣ q = {!congruence₁(𝐒) (injective(bf) (injective(Either.Right) (symmetry(_≡_) p 🝖 fxfy 🝖 q)))!}
-}

instance
  interleave-injective : ⦃ inj-af : Injective(af) ⦄ → ⦃ inj-bf : Injective(bf) ⦄ → Injective(interleave af bf)
  interleave-injective = intro interleave-injective-raw

instance
  interleave-surjective : ⦃ surj-af : Surjective(af) ⦄ → ⦃ surj-bf : Surjective(bf) ⦄ → Surjective(interleave af bf)
  Surjective.proof (interleave-surjective {af = af}{bf = bf}) {[∨]-introₗ y} with surjective(af){y}
  ... | [∃]-intro n ⦃ [≡]-intro ⦄ = [∃]-intro(2 ⋅ n) ⦃ interleave-left{n = n} ⦄
  Surjective.proof (interleave-surjective {af = af}{bf = bf}) {[∨]-introᵣ y} with surjective(bf){y}
  ... | [∃]-intro n ⦃ [≡]-intro ⦄ = [∃]-intro(𝐒(2 ⋅ n)) ⦃ interleave-right{n = n} ⦄

instance
  interleave-bijective : ⦃ bij-af : Bijective(af) ⦄ → ⦃ bij-bf : Bijective(bf) ⦄ → Bijective(interleave af bf)
  interleave-bijective {af = af}{bf = bf} = injective-surjective-to-bijective(interleave af bf) where
    instance
      inj-af : Injective(af)
      inj-af = bijective-to-injective af
    instance
      inj-bf : Injective(bf)
      inj-bf = bijective-to-injective bf
    instance
      surj-af : Surjective(af)
      surj-af = bijective-to-surjective af
    instance
      surj-bf : Surjective(bf)
      surj-bf = bijective-to-surjective bf
-}

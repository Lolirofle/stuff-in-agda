open import Type
open import Structure.Relator
open import Structure.Setoid renaming (_≡_ to _≡ₑ_)

-- TODO: Organize this module
module Structure.Sets.ZFC.Inductive {ℓₛ ℓₗ ℓₑ} {S : Type{ℓₛ}} ⦃ equiv : Equiv{ℓₑ}(S) ⦄ (_∈_ : S → S → Type{ℓₗ}) ⦃ [∈]-binaryRelator : BinaryRelator(_∈_) ⦄ where

open import Functional using (id)
open import Functional.Dependent
import      Lvl
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Structure.Relator.Proofs renaming ([≡]-binaryRelator to [≡ₑ]-binaryRelator)
open import Structure.Sets.ZFC(_∈_) ⦃ [∈]-binaryRelator ⦄
open import Structure.Sets.ZFC.Oper(_∈_)
import      Structure.Sets.Names
open        Structure.Sets.Names.From-[∈] (_∈_)
open import Structure.Sets.Quantifiers (_∈_)
open import Syntax.Function

private variable ℓ : Lvl.Level
private variable A B C D E N a b c d e x y z As : S
private variable P : S → Type{ℓ}

module _ ⦃ zfc : ZFC ⦄ where
  open ZFC(zfc)

  -- minSubset P(A) is the intersection of all subsets of A satisfying P.
  -- Semantically, minSubset P(A) is the minimal subset of A satisfying P when A satisfies P and big intersection of a set containing A preserves P.
  minSubset : (P : S → Type{ℓ}) → ⦃ rel : UnaryRelator(P) ⦄ → S → S
  minSubset P(A) = ⋂(filter P(℘(A)))

  -- The minimal subset is a subset of the given set when the given set satisfies the given property.
  minSubset-subset : ⦃ rel : UnaryRelator(P) ⦄ → P(A) → (minSubset P(A) ⊆ A)
  minSubset-subset {P = P}{A = A} pa xM = [∧]-elimᵣ([↔]-to-[→] intersection xM) filt where
    filt : (A ∈ filter P(℘(A)))
    filt = [↔]-to-[←] restricted-comprehension ([∧]-intro ℘-self pa)

  -- A subset of the minimal subset is equal to the minimal subset if it and the given set satisfies the given property.
  minSubset-subsets : ⦃ rel : UnaryRelator(P) ⦄ → P(A) → P(B) → (B ⊆ minSubset P(A)) → (B ⊇ minSubset P(A))
  minSubset-subsets {P = P}{A = A} pa pb sub cont = [∧]-elimᵣ([↔]-to-[→] (restricted-comprehension ⦃ _ ⦄) cont) (filt-pow ([∧]-intro (minSubset-subset pa ∘ sub) pb)) where
    filt-pow : ((B ⊆ A) ∧ P(B)) → (B ∈ filter P(℘(A)))
    filt-pow ([∧]-intro sub pb) = [↔]-to-[←] restricted-comprehension ([∧]-intro ([↔]-to-[←] power sub) pb)

  minSubset-satisfaction3 : ⦃ rel : UnaryRelator(P) ⦄ → (∀ₛ(℘(℘(A))) (As ↦ ((∀ₛ(As) P) → P(⋂ As)))) → P(A) → P(minSubset P(A))
  minSubset-satisfaction3 preserv p = preserv ([↔]-to-[←] power ([∧]-elimₗ ∘ [↔]-to-[→] restricted-comprehension)) ([∧]-elimᵣ ∘ [↔]-to-[→] restricted-comprehension)

  -- When the big intersection of a set containing A preserves P and A satisfies P, then the minimal subset satisfies P.
  minSubset-satisfaction : ⦃ rel : UnaryRelator(P) ⦄ → (∀{As} → (A ∈ As) → (∀ₛ(As) P) → P(⋂ As)) → P(A) → P(minSubset P(A))
  minSubset-satisfaction preserv p = preserv ([↔]-to-[←] restricted-comprehension ([∧]-intro ℘-self p)) ([∧]-elimᵣ ∘ [↔]-to-[→] restricted-comprehension)



  -- The "smallest" inductive set is the set of natural numbers.
  -- All elements which can be expressed using only 𝟎 and 𝐒.
  ℕ : S
  ℕ = ⋂(filter Inductive (℘(ω₀))) -- TODO: This pattern seems useful. See the module Inductive

  -- The relation "lesser than" in this model of ℕ.
  -- This works for all elements in ℕ by the definition of 𝟎 and 𝐒.
  _<_ : S → S → Type
  a < b = a ∈ b

  _≤_ : S → S → Type
  a ≤ b = (a < b) ∨ (a ≡ b)

  _>_ : S → S → Type
  a > b = b < a

  _≥_ : S → S → Type
  a ≥ b = b ≤ a

  infixl 2000 _<_ _≤_ _>_ _≥_

  𝕟 : S → S
  𝕟(n) = filter(_< n) ⦃ binary-unaryRelatorᵣ ⦄ (ℕ)

  -- The set ℕ contains zero and all successors.
  ℕ-inductive : Inductive(ℕ)
  ℕ-inductive = minSubset-satisfaction p infinity where
    p :  ∀{S} → (ω₀ ∈ S) → (∀ₛ(S) Inductive) → Inductive(⋂ S)
    p {S} omega ind = [∧]-intro base step where
      base : 𝟎 ∈ (⋂ S)
      base = [↔]-to-[←] intersection ([∧]-intro ([∃]-intro ω₀ ⦃ [∧]-intro omega ([∧]-elimₗ infinity) ⦄) ([∧]-elimₗ ∘ ind))
      step : (x ∈ (⋂ S)) → (𝐒(x) ∈ (⋂ S))
      step xint = [↔]-to-[←] intersection ([∧]-intro ([∃]-intro ω₀ ⦃ [∧]-intro omega ([∧]-elimᵣ infinity ([∧]-elimᵣ([↔]-to-[→] intersection xint) omega)) ⦄) (\as → [∧]-elimᵣ(ind as) ([∧]-elimᵣ([↔]-to-[→] intersection xint) as)))

  {-
    ℕ-inclusionᵣ : (x ∈ ℕ) → ∃(A ↦ ((A ⊆ ω₀) ∧ Inductive(A)) ∧ (x ∈ A)) ∧ ∀ₗ(A ↦ (((A ⊆ ω₀) ∧ Inductive(A)) → (x ∈ A)))
    ℕ-inclusionᵣ xℕ = [∧]-map ([∃]-map-proof ([∧]-map ([∧]-map ([↔]-to-[→] power) id ∘ [↔]-to-[→] restricted-comprehension) id) ∘ [↔]-to-[→] union) (\p q → p ([↔]-to-[←] restricted-comprehension ([∧]-map ([↔]-to-[←] power) id q))) ([↔]-to-[→] intersection xℕ)
  -}

  -- The natural numbers' set induction principle.
  ℕ-set-induction : Inductive(N) → (N ⊆ ℕ) → (N ⊇ ℕ)
  ℕ-set-induction = minSubset-subsets infinity

  -- The induction principle of the natural numbers for the elements in the set ℕ.
  ℕ-induction : ⦃ rel : UnaryRelator(P) ⦄ → P(𝟎) → (∀ₛ(ℕ) (n ↦ (P(n) → P(𝐒(n))))) → (∀ₛ(ℕ) P)
  ℕ-induction {P = P} pz ps = [∧]-elimᵣ ∘ [↔]-to-[→] restricted-comprehension ∘ Pset-super where
    Pset : S
    Pset = filter P(ℕ)

    Pset-𝟎 : (𝟎 ∈ Pset)
    Pset-𝟎 = [↔]-to-[←] restricted-comprehension ([∧]-intro ([∧]-elimₗ ℕ-inductive) pz)

    Pset-𝐒 : ∀ₛ(Pset) (n ↦ (𝐒(n) ∈ Pset))
    Pset-𝐒 {n} nPset =
      let Pn : P(n)
          Pn = [∧]-elimᵣ([↔]-to-[→] restricted-comprehension nPset)

          nℕ : (n ∈ ℕ)
          nℕ = [∧]-elimₗ([↔]-to-[→] restricted-comprehension nPset)

      in  [↔]-to-[←] restricted-comprehension ([∧]-intro ([∧]-elimᵣ ℕ-inductive nℕ) (ps nℕ Pn))

    Pset-super : ℕ ⊆ Pset
    Pset-super = ℕ-set-induction ([∧]-intro Pset-𝟎 Pset-𝐒) ([∧]-elimₗ ∘ [↔]-to-[→] restricted-comprehension)
    

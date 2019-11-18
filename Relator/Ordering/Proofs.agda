module Relator.Ordering.Proofs where

open import Functional
open import Logic
open import Logic.Classical
open import Logic.Propositional
open import Logic.Propositional.Theorems
open import Type
import      Relator.Ordering
open import Structure.Relator.Ordering
import      Structure.Relator.Names as Names
open import Structure.Relator.Properties
open import Syntax.Transitivity

module From-[≤] {ℓ₁ ℓ₂} {T : Type{ℓ₁}} (_≤_ : T → T → Stmt{ℓ₂}) where
  open        Relator.Ordering.From-[≤] (_≤_)
  open import Sets.Setoid

  [≤][>]-not : ∀{a b} → (a ≤ b) → (a > b) → ⊥
  [≤][>]-not = apply

  [≥][<]-not : ∀{a b} → (a ≥ b) → (a < b) → ⊥
  [≥][<]-not = apply

  module _ ⦃ _ : Equiv(T) ⦄ ⦃ _ : Weak.TotalOrder(_≤_)(_≡_) ⦄ where
    [<]-to-[≤] : Names.Subrelation(_<_)(_≤_)
    [<]-to-[≤] {a} {b} nba with converseTotal(_≤_){a}{b}
    [<]-to-[≤] {a} {b} nba | [∨]-introₗ ab = ab
    [<]-to-[≤] {a} {b} nba | [∨]-introᵣ ba = [⊥]-elim(nba ba)
    instance
      [<][≤]-sub : (_<_) ⊆₂ (_≤_)
      _⊆₂_.proof [<][≤]-sub = [<]-to-[≤]

    [>]-to-[≥] : Names.Subrelation(_>_)(_≥_)
    [>]-to-[≥] = [<]-to-[≤]
    [>][≥]-sub : (_>_) ⊆₂ (_≥_)
    _⊆₂_.proof [>][≥]-sub = [>]-to-[≥]

    instance
      [<]-irreflexivity : Irreflexivity(_<_)
      Irreflexivity.proof [<]-irreflexivity = [¬¬]-intro(reflexivity(_≤_))

    instance
      [<]-transitivity : Transitivity(_<_)
      Transitivity.proof [<]-transitivity {a} {b} {c} nba ncb ca = [≤][>]-not (transitivity(_≤_) ca ([<]-to-[≤] nba)) ncb

    instance
      [<]-asymmetry : Asymmetry(_<_) -- TODO: Proof of this property is independent of the model. Actually, many of them here are
      [<]-asymmetry = [irreflexivity,transitivity]-to-asymmetry

    [<]-strictOrder : Strict.Order(_<_)
    [<]-strictOrder = Strict.Order.intro

    module _ ⦃ _ : (_≡_) ⊆₂ (_≤_) ⦄ where -- TODO: Consider including this in weak orders
      [≡]-to-[≥] : Names.Subrelation(_≡_)(_≥_)
      [≡]-to-[≥] = sub₂(_≡_)(_≤_) ∘ symmetry(_≡_)
      instance
        [≡][≥]-sub : (_≡_) ⊆₂ (_≥_)
        _⊆₂_.proof [≡][≥]-sub = [≡]-to-[≥]

      [≡][>]-not : ∀{a b} → (a ≡ b) → (a > b) → ⊥
      [≡][>]-not eq gt = [≤][>]-not (sub₂(_≡_)(_≤_) eq) gt

      [≡][<]-not : ∀{a b} → (a ≡ b) → (a < b) → ⊥
      [≡][<]-not eq lt = [≤][>]-not ([≡]-to-[≥] eq) lt

      module _ ⦃ [≡]-classical : Classical₂(_≡_) ⦄ where
        [≤]-or-[>] : ∀{a b} → (a ≤ b) ∨ (a > b)
        [≤]-or-[>] {a} {b} with converseTotal(_≤_){a}{b}
        [≤]-or-[>] {a} {b} | [∨]-introₗ ab = [∨]-introₗ ab
        [≤]-or-[>] {a} {b} | [∨]-introᵣ ba with excluded-middle ⦃ [≡]-classical {a}{b} ⦄
        [≤]-or-[>] {a} {b} | [∨]-introᵣ ba | [∨]-introₗ eqab  = [∨]-introₗ (sub₂(_≡_)(_≤_) eqab)
        [≤]-or-[>] {a} {b} | [∨]-introᵣ ba | [∨]-introᵣ neqab = [∨]-introᵣ (ab ↦ neqab(antisymmetry(_≤_)(_≡_) ab ba))

        instance
          [≤]-classical : Classical₂(_≤_)
          excluded-middle ⦃ [≤]-classical ⦄ = [≤]-or-[>]

        [≥]-or-[<] : ∀{a b} → (a ≥ b) ∨ (a < b)
        [≥]-or-[<] = [≤]-or-[>]

        [≥]-classical : Classical₂(_≥_)
        excluded-middle ⦃ [≥]-classical ⦄ = [≥]-or-[<]

        instance
          [<]-classical : Classical₂(_<_)
          excluded-middle ⦃ [<]-classical {a}{b} ⦄ with [≤]-or-[>] {b}{a}
          excluded-middle ⦃ [<]-classical {a}{b} ⦄ | [∨]-introₗ x = [∨]-introᵣ ([¬¬]-intro x)
          excluded-middle ⦃ [<]-classical {a}{b} ⦄ | [∨]-introᵣ x = [∨]-introₗ x

        [>]-classical : Classical₂(_>_)
        [>]-classical = [<]-classical

        [≤]-to-[<][≡] : ∀{a b} → (a ≤ b) → ((a < b) ∨ (a ≡ b))
        [≤]-to-[<][≡] {a} {b} ab with excluded-middle ⦃ [≡]-classical {a}{b} ⦄
        [≤]-to-[<][≡] {a} {b} ab | [∨]-introₗ eq = [∨]-introᵣ eq
        [≤]-to-[<][≡] {a} {b} ab | [∨]-introᵣ ne = [∨]-introₗ (ba ↦ ne(antisymmetry(_≤_)(_≡_) ab ba))

        [≥]-to-[>][≡] : ∀{a b} → (a ≥ b) → ((a > b) ∨ (a ≡ b))
        [≥]-to-[>][≡] ab = [∨]-map id (symmetry(_≡_)) ([≤]-to-[<][≡] ab)

    -- [<]-trichotomy : ∀{a b} → (a < b) ∨ (b < a) ∨ (a ≡ b)
    -- [<]-trichotomy {a} {b} = {!!}

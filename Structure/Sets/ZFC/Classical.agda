open import Type
open import Structure.Relator
open import Structure.Setoid renaming (_≡_ to _≡ₑ_)

module Structure.Sets.ZFC.Classical {ℓₛ ℓₗ ℓₑ} {S : Type{ℓₛ}} ⦃ equiv : Equiv{ℓₑ}(S) ⦄ (_∈_ : S → S → Type{ℓₗ}) ⦃ [∈]-binaryRelator : BinaryRelator(_∈_) ⦄ where

open import Data.Either as Either using ()
open import Functional
open import Logic.Classical
open import Logic.Predicate
open import Logic.Propositional
open import Logic.Propositional.Theorems
import      Lvl
open import Structure.Operator
open import Structure.Relator.Proofs
open import Structure.Relator.Properties
import      Structure.Sets.Names
open        Structure.Sets.Names.From-[∈] (_∈_)
open        Structure.Sets.Names.Relations (_∈_)
open import Structure.Sets.ZFC(_∈_) ⦃ [∈]-binaryRelator ⦄
open import Syntax.Function
open import Syntax.Implication
open import Syntax.Transitivity

private variable ℓ : Lvl.Level
private variable T A B : Type{ℓ}
private variable x : S

module _ ⦃ zfc : ZFC ⦄ where
  open ZFC(zfc)

  -- ZFC implies excluded middle.
  -- Note that this only requires the following set related axioms:
  -- • Set extensionality (Not really neccessary if every equality is replaced with set equality instead).
  -- • Axiom of choice (TODO: Is this really neccessary? The proof only uses the choice function on finite sets? Further investigation on choice functions for finite sets would clear this up).
  -- • Choice functions are functions.
  -- • Restricted set comprehension.
  -- • Existence of at least two different sets (In this proof, ∅ and {∅} (𝑇 and 𝐹) is used).
  -- • Existence of a set containing the two different sets, and the existence of all subsets of this set.
  -- Also called: Diaconescu's theorem, Goodman–Myhill theorem.
  excluded-middle-by-choice : ∀{P : Type{ℓ}} → Classical(P)
  excluded-middle-by-choice{P = P} = intro $ᵢₙₛₜ
    let
      instance
        pos-rel : UnaryRelator(x ↦ P ∨ (x ≡ 𝑇))
        pos-rel = [∨]-unaryRelator ⦃ rel-Q = binary-unaryRelatorᵣ ⦄

      instance
        neg-rel : UnaryRelator(x ↦ P ∨ (x ≡ 𝐹))
        neg-rel = [∨]-unaryRelator ⦃ rel-Q = binary-unaryRelatorᵣ ⦄

      pos = filter (x ↦ P ∨ (x ≡ 𝑇)) BoolSet
      neg = filter (x ↦ P ∨ (x ≡ 𝐹)) BoolSet

      -- The contents of pos by definition. A subset of BoolSet which is equal to BoolSet when P, {𝑇} otherwise.
      pos-containment : (x ∈ pos) ↔ (x ∈ BoolSet) ∧ (P ∨ (x ≡ 𝑇))
      pos-containment = restricted-comprehension

      -- The contents of neg by definition. A subset of BoolSet which is equal to BoolSet when P, {𝐹} otherwise.
      neg-containment : (x ∈ neg) ↔ (x ∈ BoolSet) ∧ (P ∨ (x ≡ 𝐹))
      neg-containment = restricted-comprehension

      -- pos is non-empty because it should at least contain 𝑇 from filtering BoolSet.
      instance
        ne-pos : NonEmpty(pos)
        ne-pos = [↔]-to-[←] (nonEmpty-filter) ([∃]-intro 𝑇 ⦃ [∧]-intro 𝑇-in-BoolSet ([∨]-introᵣ (\{_} → [↔]-reflexivity)) ⦄)

      -- neg is non-empty because it should at least contain 𝐹 from filtering BoolSet.
      instance
        ne-neg : NonEmpty(neg)
        ne-neg = [↔]-to-[←] (nonEmpty-filter) ([∃]-intro 𝐹 ⦃ [∧]-intro 𝐹-in-BoolSet ([∨]-introᵣ (\{_} → [↔]-reflexivity)) ⦄)

      -- Chooses an element in respective sets pos and neg.
      pos-choose = choose (pair pos neg) pos
      neg-choose = choose (pair pos neg) neg

      -- By definition of pos, either P holds or pos-choose have to be 𝑇.
      pos-choice : P ∨ (pos-choose ≡ 𝑇)
      pos-choice = [∧]-elimᵣ ([↔]-to-[→] pos-containment (choice {pair pos neg} {pos} ⦃ ne-pos ⦄ ⦃ pair-contains-left ⦄))

      -- By definition of neg, either P holds or neg-choose have to be 𝐹.
      neg-choice : P ∨ (neg-choose ≡ 𝐹)
      neg-choice = [∧]-elimᵣ ([↔]-to-[→] neg-containment (choice {pair pos neg} {neg} ⦃ ne-neg ⦄ ⦃ pair-contains-right ⦄))
    in
      • ( -- Contrapositive of the argument below states that if pos-choose and neg-choose is inequal, then (¬ P)
        (_⇒ -- When P holds, both pos and neg is BoolSet, so they are equal. The pos-choose and neg-choose is the choice function applied to the equal sets pos and neg respectively, and because choose is a function (it respects equality, specifically set equality), pos-choose and neg-choose is also equal.
          P                          ⇒-[ (\p {x} → [↔]-transitivity (pos-containment {x}) ([↔]-transitivity ([∧]-mapᵣ-[↔] ([↔]-intro (const([∨]-introₗ p)) (const([∨]-introₗ p)))) ([↔]-symmetry (neg-containment {x})))) ]
          (pos ≡ neg)                ⇒-[ [↔]-to-[←] set-extensionality ]
          (pos ≡ₑ neg)               ⇒-[ congruence₂(choose) (reflexivity(_≡ₑ_)) ]
          (pos-choose ≡ₑ neg-choose) ⇒-end
        ) ⇒
        (P → (pos-choose ≡ₑ neg-choose))    ⇒-[ contrapositiveᵣ ]
        ((¬ P) ← (pos-choose ≢ neg-choose)) ⇒-end
      )
      • ( -- The case other than P is that pos and neg only contains 𝑇 and 𝐹 respectively. This forces pos-choose and neg-choose to be 𝑇 and 𝐹 respectively, which means that they are inequal.
        • pos-choice
        • neg-choice
        ⇒₂-[ [∧]-intro ]
        (P ∨ (pos-choose ≡ 𝑇)) ∧ (P ∨ (neg-choose ≡ 𝐹)) ⇒-[ [↔]-to-[←] [∨][∧]-distributivityₗ ]
        P ∨ ((pos-choose ≡ 𝑇) ∧ (neg-choose ≡ 𝐹))       ⇒-[ Either.mapRight (\{([∧]-intro p0 n1) → [≡][≢]-semitransitivityᵣ([≡][≢]-semitransitivityₗ ([↔]-to-[←] set-extensionality p0) zero-one-ineq) (symmetry(_≡ₑ_) ([↔]-to-[←] set-extensionality n1))}) ]
        P ∨ (pos-choose ≢ neg-choose)                   ⇒-end
      )
      ⇒₂-[ Either.mapRight ]
      (P ∨ (¬ P)) ⇒-end

module Formalization.ClassicalPropositionalLogic.NaturalDeduction.Proofs where

open import Data.Boolean
open import Data.Either
open import Functional
open import Formalization.ClassicalPropositionalLogic.NaturalDeduction
open import Formalization.ClassicalPropositionalLogic.Place
open import Formalization.ClassicalPropositionalLogic.Syntax
import      Lvl
open import Logic
import      Logic.Propositional as Meta
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _∪•_ ; _∖_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇]) renaming (•_ to singleton ; _≡_ to _≡ₛ_)
open import Type

private variable ℓₚ ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable T A B : Type{ℓ}
private variable P : Type{ℓₚ}
private variable φ ψ γ : Formula(P)
private variable Γ : Formulas(P){ℓ}
private variable f : A → B
private variable s e : Bool
private variable p : P

module _ where
  [¬]-intro-converse : ((Γ ∪ singleton(φ)) ⊢ ⊥) ← (Γ ⊢ (¬ φ))
  [¬]-intro-converse {Γ = Γ}{φ = φ} Γ¬φ = [⊥]-intro (direct (Right [≡]-intro)) (weaken-union Γ¬φ)

  excluded-middle : Γ ⊢ (φ ∨ (¬ φ))
  excluded-middle =
    ([¬¬]-elim
      ([¬]-intro
        ([⊥]-intro
          ([∨]-introᵣ
            ([¬]-intro
              ([⊥]-intro
                ([∨]-introₗ (direct (Right [≡]-intro)))
                (direct (Left (Right [≡]-intro)))
              )
            )
          )
          (direct (Right [≡]-intro))
        )
      )
    )

  [→]-disjunctive-form : (Γ ⊢ (φ ⟶ ψ)) Meta.↔ (Γ ⊢ ((¬ φ) ∨ ψ))
  [→]-disjunctive-form = Meta.[↔]-intro l r where
    l = [∨]-elim
      ([⟶]-intro ([⊥]-elim ([⊥]-intro
        (direct (Right [≡]-intro))
        (direct (Left (Right [≡]-intro)))
      )))
      ([⟶]-intro (direct (Left (Right [≡]-intro))))
    r = pq ↦
      ([∨]-elim
        ([∨]-introᵣ ([⟶]-elim (direct (Right [≡]-intro)) (weaken Left pq)))
        ([∨]-introₗ (direct (Right [≡]-intro)))
        excluded-middle
      )

  [⟷]-negated : (Γ ⊢ (φ ⟷ ψ)) → (Γ ⊢ ((¬ φ) ⟷ (¬ ψ)))
  [⟷]-negated p = [⟷]-intro
    ([¬]-intro ([⊥]-intro ([⟷]-elimᵣ (direct (Right [≡]-intro)) (weaken (Left ∘ Left) p)) (direct (Left (Right [≡]-intro)))))
    (([¬]-intro ([⊥]-intro ([⟷]-elimₗ (direct (Right [≡]-intro)) (weaken (Left ∘ Left) p)) (direct (Left (Right [≡]-intro))))))

  [⟷]-conjunction-disjunction-negation : (Γ ⊢ (φ ⟷ ψ)) Meta.↔ (Γ ⊢ ((φ ∧ ψ) ∨ ((¬ φ) ∧ (¬ ψ))))
  [⟷]-conjunction-disjunction-negation = Meta.[↔]-intro l r where
    l = [∨]-elim
      ([⟷]-intro
        ([∧]-elimₗ (direct (Left (Right [≡]-intro))))
        ([∧]-elimᵣ (direct (Left (Right [≡]-intro))))
      )
      ([⟷]-intro
        ([⊥]-elim ([⊥]-intro (direct (Right [≡]-intro)) ([∧]-elimᵣ (direct (Left (Right [≡]-intro))))))
        ([⊥]-elim ([⊥]-intro (direct (Right [≡]-intro)) ([∧]-elimₗ (direct (Left (Right [≡]-intro))))))
      )
    r = p ↦ [∨]-elim
      ([∨]-introₗ ([∧]-intro
        (direct (Right [≡]-intro))
        ([⟷]-elimᵣ (direct (Right [≡]-intro)) (weaken Left p))
      ))
      ([∨]-introᵣ ([∧]-intro
        (direct (Right [≡]-intro))
        ([⟷]-elimᵣ (direct (Right [≡]-intro)) (weaken Left ([⟷]-negated p)))
      ))
      excluded-middle

-- TODO: The two proofs contain very similar cases (the structure is identical in all cases). Are there any good ways to generalize? Maybe by using the strict variants?
positive-congruence : Positive(P) f → (Γ ⊢ (φ ⟶ ψ) ⟶ (f(φ) ⟶ f(ψ)))
negative-congruence : Negative(P) f → (Γ ⊢ (φ ⟶ ψ) ⟶ (f(φ) ⟵ f(ψ)))

positive-congruence identity           = [⟶]-intro ([⟶]-intro ([⟶]-elim (direct (Right [≡]-intro)) (direct (Left (Right [≡]-intro)))))
positive-congruence (conjunctionₗ ctx) =
  [⟶]-intro ([⟶]-intro ([∧]-intro
    ([∧]-elimₗ (direct (Right [≡]-intro)))
    ([⟶]-elim ([∧]-elimᵣ (direct (Right [≡]-intro))) ([⟶]-elim (direct (Left (Right [≡]-intro))) (positive-congruence ctx)))
  ))
positive-congruence (conjunctionᵣ ctx) =
  [⟶]-intro ([⟶]-intro ([∧]-intro
    ([⟶]-elim ([∧]-elimₗ (direct (Right [≡]-intro))) ([⟶]-elim (direct (Left (Right [≡]-intro))) (positive-congruence ctx)))
    ([∧]-elimᵣ (direct (Right [≡]-intro)))
  ))
positive-congruence (disjunctionₗ ctx) =
  [⟶]-intro ([⟶]-intro ([∨]-elim
    ([∨]-introₗ (direct (Right [≡]-intro)))
    ([∨]-introᵣ ([⟶]-elim (direct (Right [≡]-intro)) ([⟶]-elim (direct (Left (Left (Right [≡]-intro)))) (positive-congruence ctx))))
    (direct (Right [≡]-intro))
  ))
positive-congruence (disjunctionᵣ ctx) =
  [⟶]-intro ([⟶]-intro ([∨]-elim
    ([∨]-introₗ ([⟶]-elim (direct (Right [≡]-intro)) ([⟶]-elim (direct (Left (Left (Right [≡]-intro)))) (positive-congruence ctx))))
    ([∨]-introᵣ (direct (Right [≡]-intro)))
    (direct (Right [≡]-intro))
  ))
positive-congruence (implicationₗ ctx) =
  [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim
    ([⟶]-elim (direct(Right [≡]-intro)) (direct (Left (Right [≡]-intro))))
    ([⟶]-elim (direct (Left (Left (Right [≡]-intro)))) (positive-congruence ctx))
  )))
positive-congruence (implicationᵣ ctx) =
  [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim
    ([⟶]-elim (direct (Right [≡]-intro)) ([⟶]-elim (direct (Left (Left (Right [≡]-intro)))) (negative-congruence ctx)))
    (direct (Left (Right [≡]-intro)))
  )))

negative-congruence (conjunctionₗ ctx) =
  [⟶]-intro ([⟶]-intro ([∧]-intro
    ([∧]-elimₗ (direct (Right [≡]-intro)))
    ([⟶]-elim ([∧]-elimᵣ (direct (Right [≡]-intro))) ([⟶]-elim (direct (Left (Right [≡]-intro))) (negative-congruence ctx)))
  ))
negative-congruence (conjunctionᵣ ctx) =
  [⟶]-intro ([⟶]-intro ([∧]-intro
    ([⟶]-elim ([∧]-elimₗ (direct (Right [≡]-intro))) ([⟶]-elim (direct (Left (Right [≡]-intro))) (negative-congruence ctx)))
    ([∧]-elimᵣ (direct (Right [≡]-intro)))
  ))
negative-congruence (disjunctionₗ ctx) =
  [⟶]-intro ([⟶]-intro ([∨]-elim
    ([∨]-introₗ (direct (Right [≡]-intro)))
    ([∨]-introᵣ ([⟶]-elim (direct (Right [≡]-intro)) ([⟶]-elim (direct (Left (Left (Right [≡]-intro)))) (negative-congruence ctx))))
    (direct (Right [≡]-intro))
  ))
negative-congruence (disjunctionᵣ ctx) =
  [⟶]-intro ([⟶]-intro ([∨]-elim
    ([∨]-introₗ ([⟶]-elim (direct (Right [≡]-intro)) ([⟶]-elim (direct (Left (Left (Right [≡]-intro)))) (negative-congruence ctx))))
    ([∨]-introᵣ (direct (Right [≡]-intro)))
    (direct (Right [≡]-intro))
  ))
negative-congruence (implicationₗ ctx) =
  [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim
    ([⟶]-elim (direct(Right [≡]-intro)) (direct (Left (Right [≡]-intro))))
    ([⟶]-elim (direct (Left (Left (Right [≡]-intro)))) (negative-congruence ctx))
  )))
negative-congruence (implicationᵣ ctx) =
  [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim
    ([⟶]-elim (direct (Right [≡]-intro)) ([⟶]-elim (direct (Left (Left (Right [≡]-intro)))) (positive-congruence ctx)))
    (direct (Left (Right [≡]-intro)))
  )))

-- TODO: Mainly for results in minimal logic
data NegativeFragment {P : Type{ℓₚ}} : Formula(P) → Type{Lvl.of(P)} where
  atom   : NegativeFragment(¬(• p))
  bottom : NegativeFragment(⊥)
  top    : NegativeFragment(⊤)
  neg    : NegativeFragment(φ) → NegativeFragment(¬ φ)
  and    : NegativeFragment(φ) → NegativeFragment(ψ) → NegativeFragment(φ ∧ ψ)
  impl   : NegativeFragment(φ) → NegativeFragment(ψ) → NegativeFragment(φ ⟶ ψ)
  eq     : NegativeFragment(φ) → NegativeFragment(ψ) → NegativeFragment(φ ⟷ ψ)

open import Functional
open import Type.Dependent
open import Type.Dependent.Functions

module GGNegativeTranslation where
  trans : Formula(P) → Formula(P)
  trans (• p)   = ¬(¬(• p))
  trans ⊤       = ⊤
  trans ⊥       = ⊥
  trans (¬ φ)   = ¬(trans φ)
  trans (φ ∧ ψ) = (trans φ) ∧ (trans ψ)
  trans (φ ∨ ψ) = ¬((¬(trans φ)) ∧ (¬(trans ψ)))
  trans (φ ⟶ ψ) = (trans φ) ⟶ (trans ψ)
  trans (φ ⟷ ψ) = (trans φ) ⟷ (trans ψ)

  trans-negativeFragment : NegativeFragment(trans(φ))
  trans-negativeFragment {φ = • p}   = neg atom
  trans-negativeFragment {φ = ⊤}     = top
  trans-negativeFragment {φ = ⊥}     = bottom
  trans-negativeFragment {φ = ¬ φ}   = neg trans-negativeFragment
  trans-negativeFragment {φ = φ ∧ ψ} = and trans-negativeFragment trans-negativeFragment
  trans-negativeFragment {φ = φ ∨ ψ} = neg(and(neg trans-negativeFragment) (neg trans-negativeFragment))
  trans-negativeFragment {φ = φ ⟶ ψ} = impl trans-negativeFragment trans-negativeFragment
  trans-negativeFragment {φ = φ ⟷ ψ} = eq trans-negativeFragment trans-negativeFragment

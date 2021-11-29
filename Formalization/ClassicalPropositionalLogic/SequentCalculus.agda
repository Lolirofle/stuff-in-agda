open import Type
open import Logic.Classical as Logic using (Classical)
open import Logic.Predicate as Logic using ()

module Formalization.ClassicalPropositionalLogic.SequentCalculus ⦃ classical : ∀{ℓ} → Logic.∀ₗ(Classical{ℓ}) ⦄ where

import      Lvl
open import Data
open import Data.Boolean
import      Data.Boolean.Operators
open import Data.Boolean.Stmt
open import Data.Either as Either using (_‖_ ; Left ; Right)
open import Data.List
open import Data.List.Functions using () renaming (singleton to · ; _++_ to _∪_)
open import Data.List.Relation.Permutation
open import Data.Tuple as Tuple using (_⨯_ ; _,_)
private module BoolOp = Data.Boolean.Operators.Logic
open import Functional as Fn
open import Function.Names using (_⊜_)
open import Logic
open import Logic.Propositional as Logic using (_←_)
open import Logic.Propositional.Theorems as Logic using ()
open import Logic.Predicate.Theorems as Logic using ()
open import Relator.Equals renaming (_≡_ to _≡ₑ_)
open import Relator.Equals.Proofs
open import Relator.Equals.Proofs.Equiv
open import Structure.Relator.Properties
open import Syntax.Function
open import Syntax.Type
open import Syntax.Implication hiding (_⇒_)
open import Type.Size.Countable

private variable ℓₚ ℓ ℓ₁ ℓ₂ : Lvl.Level

open import Formalization.ClassicalPropositionalLogic.Syntax
open import Formalization.ClassicalPropositionalLogic.Syntax.Proofs
open import Formalization.ClassicalPropositionalLogic.Semantics
open import Formalization.ClassicalPropositionalLogic.Semantics.Proofs
import      Formalization.ClassicalPropositionalLogic.TruthTable as TruthTable

_∪·_ : ∀{T : Type{ℓ}} → List(T) → T → List(T)
_∪·_ = Fn.swap(_⊰_)
infixl 1000 _∪·_

module _ {ℓₚ} {P : Type{ℓₚ}} where
  private variable Γ Γ₁ Γ₂ Γ₃ Δ Δ₁ Δ₂ Δ₃ : List(Formula(P))
  private variable φ φ₁ φ₂ ψ A B C : Formula(P)
  private variable p : P

  data _⇒_ : List(Formula(P)) → List(Formula(P)) → Stmt{Lvl.𝐒(ℓₚ)} where
    axiom : ((·(• p)) ⇒ (·(• p)))

    weakenₗ : (Γ ⇒ Δ) → ((Γ ∪· A) ⇒ Δ)
    permuteₗ : .(Γ₁ permutes Γ₂) → (Γ₁ ⇒ Δ) → (Γ₂ ⇒ Δ)
    contractₗ : ((Γ ∪· A ∪· A) ⇒ Δ) → ((Γ ∪· A) ⇒ Δ)
    ⊥ₗ : (Γ ∪· ⊥) ⇒ ∅
    ∧ₗₗ : ((Γ ∪· A) ⇒ Δ) → ((Γ ∪· (A ∧ B)) ⇒ Δ)
    ∧ₗᵣ : ((Γ ∪· B) ⇒ Δ) → ((Γ ∪· (A ∧ B)) ⇒ Δ)
    ∨ₗ : ((Γ ∪· A) ⇒ Δ) → ((Γ ∪· B) ⇒ Δ) → ((Γ ∪· (A ∨ B)) ⇒ Δ)
    ⟶ₗ : (Γ ⇒ (Δ ∪· A)) → ((Γ ∪· B) ⇒ Δ) → ((Γ ∪· (A ⟶ B)) ⇒ Δ)
    ¬ₗ : (Γ ⇒ (Δ ∪· A)) → ((Γ ∪· (¬ A)) ⇒ Δ)

    weakenᵣ : (Γ ⇒ Δ) → (Γ ⇒ (Δ ∪· A))
    permuteᵣ : .(Δ₁ permutes Δ₂) → (Γ ⇒ Δ₁) → (Γ ⇒ Δ₂)
    contractᵣ : (Γ ⇒ (Δ ∪· A ∪· A)) → (Γ ⇒ (Δ ∪· A))
    ⊤ᵣ : ∅ ⇒ (Δ ∪· ⊤)
    ∧ᵣ : (Γ ⇒ (Δ ∪· A)) → (Γ ⇒ (Δ ∪· B)) → (Γ ⇒ (Δ ∪· (A ∧ B)))
    ∨ᵣₗ : (Γ ⇒ (Δ ∪· A)) → (Γ ⇒ (Δ ∪· (A ∨ B)))
    ∨ᵣᵣ : (Γ ⇒ (Δ ∪· B)) → (Γ ⇒ (Δ ∪· (A ∨ B)))
    ⟶ᵣ : ((Γ ∪· A) ⇒ (Δ ∪· B)) → (Γ ⇒ (Δ ∪· (A ⟶ B)))
    ¬ᵣ : ((Γ ∪· A) ⇒ Δ) → (Γ ⇒ (Δ ∪· (¬ A)))

  permute : .(Γ₁ permutes Γ₂) → .(Δ₁ permutes Δ₂) → (Γ₁ ⇒ Δ₁) → (Γ₂ ⇒ Δ₂)
  permute permΓ permΔ ΓΔ = permuteₗ permΓ (permuteᵣ permΔ ΓΔ)

  open import Data.List.Equiv.Id
  open import Data.List.Relation.Membership
  open import Data.List.Proofs
  open import Structure.Operator.Properties

  refl : (· A) ⇒ (· A)
  refl {• x} = axiom
  refl {⊤} = weakenₗ ⊤ᵣ
  refl {⊥} = weakenᵣ ⊥ₗ
  refl {¬ A} = ¬ᵣ (permuteₗ(_permutes_.swap) (¬ₗ refl))
  refl {A ∧ B} = ∧ᵣ (∧ₗₗ refl) (∧ₗᵣ refl)
  refl {A ∨ B} = ∨ₗ (∨ᵣₗ refl) (∨ᵣᵣ refl)
  refl {A ⟶ B} = ⟶ᵣ (permuteₗ(_permutes_.swap) (⟶ₗ (permuteᵣ(_permutes_.swap) (weakenᵣ refl)) (permuteₗ(_permutes_.swap) (weakenₗ refl))))
  refl {A ⟷ B} = {!!}

  --[⇒]-trans : (Γ₁ ⇒ Γ₂) → (Γ₂ ⇒ Γ₃) → (Γ₁ ⇒ Γ₃)
  --[⇒]-trans p12 p23 = {!-c -t 10!}

  [⇒][++]ᵣ-weakenₗ : (Γ₂ ⇒ Δ) → ((Γ₁ ∪ Γ₂) ⇒ Δ)
  [⇒][++]ᵣ-weakenₗ {Γ₁ = ∅}       p = p
  [⇒][++]ᵣ-weakenₗ {Γ₁ = φ₁ ⊰ Γ₁} p = weakenₗ([⇒][++]ᵣ-weakenₗ {Γ₁ = Γ₁} p)

  [⇒][++]ₗ-weakenₗ : (Γ₁ ⇒ Δ) → ((Γ₁ ∪ Γ₂) ⇒ Δ)
  [⇒][++]ₗ-weakenₗ {Γ₁ = Γ₁}{Δ = Δ}{Γ₂ = Γ₂} Γ₁Δ = permuteₗ (sub₂(_≡ₑ_)(_permutes_) (commutativity(_∪_) ⦃ {!!} ⦄ {Γ₂}{Γ₁})) ([⇒][++]ᵣ-weakenₗ {Γ₁ = Γ₂} Γ₁Δ)

  [⇒][++]-weakenᵣ : (Γ ⇒ Δ₂) → (Γ ⇒ (Δ₁ ∪ Δ₂))
  [⇒][++]-weakenᵣ {Δ₁ = ∅}       p = p
  [⇒][++]-weakenᵣ {Δ₁ = φ₁ ⊰ Δ₁} p = weakenᵣ([⇒][++]-weakenᵣ {Δ₁ = Δ₁} p)

  [⇒][⊥]-arbitrary : ((Γ ∪· ⊥) ⇒ Δ)
  [⇒][⊥]-arbitrary {Γ = Γ}{Δ = Δ} = permuteᵣ (sub₂(_≡ₑ_)(_permutes_) (identityᵣ(_∪_)(∅))) ([⇒][++]-weakenᵣ{Δ₂ = ∅}{Δ} ⊥ₗ)

  [⇒]-nonempty-reflexivity : ((φ ⊰ Γ) ⇒ (φ ⊰ Γ))
  [⇒]-nonempty-reflexivity {Γ = ∅}     = refl
  [⇒]-nonempty-reflexivity {Γ = φ ⊰ Γ} = weakenₗ (weakenᵣ ([⇒]-nonempty-reflexivity {Γ = Γ}))

  {- TODO: Maybe not
  [⇒]-symmetric-by-side : ((Γ₁ ⇒ Δ) → (Γ₂ ⇒ Δ)) → ((Δ ⇒ Γ₂) → (Δ ⇒ Γ₁))
  [⇒]-symmetric-by-side p axiom = {!!}
  [⇒]-symmetric-by-side p (weakenₗ q) = {!!}
  [⇒]-symmetric-by-side p (permuteₗ x q) = {!!}
  [⇒]-symmetric-by-side p (contractₗ q) = {!!}
  [⇒]-symmetric-by-side p ⊥ₗ = [⇒][⊥]-arbitrary
  [⇒]-symmetric-by-side p (∧ₗₗ q) = {!!}
  [⇒]-symmetric-by-side p (∧ₗᵣ q) = {!!}
  [⇒]-symmetric-by-side p (∨ₗ q q₁) = {!!}
  [⇒]-symmetric-by-side p (⟶ₗ q q₁) = {!!}
  [⇒]-symmetric-by-side p (weakenᵣ q) = {!!}
  [⇒]-symmetric-by-side p (permuteᵣ x q) = {!!}
  [⇒]-symmetric-by-side p (contractᵣ q) = [⇒]-symmetric-by-side (weakenₗ ∘ p) q
  [⇒]-symmetric-by-side p (∧ᵣ q q₁) = {!!}
  [⇒]-symmetric-by-side p (∨ᵣₗ q) = {!!}
  [⇒]-symmetric-by-side p (∨ᵣᵣ q) = {!!}
  [⇒]-symmetric-by-side p (⟶ᵣ q) = {!!}
  -}

  open import Structure.Function

  [⇒]-super : ((Γ₁ ∪· φ₁) ⊇ (Γ₂ ∪· φ₂)) → ((Γ₁ ∪· φ₁) ⇒ (Γ₂ ∪· φ₂))
  [⇒]-super {Γ₁ = Γ₁}      {Γ₂ = φ₂ ⊰ Γ₂}    p = weakenᵣ ([⇒]-super {Γ₁ = Γ₁} {Γ₂ = Γ₂} (p ∘ skip))
  [⇒]-super {Γ₁ = ∅}       {Γ₂ = ∅}          p with use [≡]-intro ← p (use [≡]-intro) = refl
  [⇒]-super {Γ₁ = φ₁ ⊰ Γ₁} {Γ₂ = ∅}{φ₂ = φ₂} p with p (use [≡]-intro)
  ... | use [≡]-intro = permuteₗ Proofs.postpend-prepend-permutes (permuteₗ(sub₂(_≡ₑ_)(_permutes_) (symmetry(_≡ₑ_) (congruence₁(φ₁ ⊰_) (postpend-[++] {a = φ₂}{l = Γ₁})))) (weakenₗ ([⇒][++]ᵣ-weakenₗ{Γ₁ = Γ₁} refl)))
  ... | skip q = weakenₗ([⇒]-super {Γ₁ = Γ₁} {Γ₂ = ∅} \{(use [≡]-intro) → q ; (skip ())})

  [⇒]-membership : (φ ∈ Γ) → (Γ ⇒ (· φ))
  [⇒]-membership (use [≡]-intro) = [⇒][++]ₗ-weakenₗ refl
  [⇒]-membership (skip p) = weakenₗ([⇒]-membership p)

  Inconsistent : List(Formula(P)) → Type
  Inconsistent(Γ) = Γ ⇒ ∅

  test : ∅ ⇒ ·((A ∧ B) ⟶ A)
  test {A = A}{B = B} =
    refl                ⇒-start
    ((· A) ⇒ (· A))      ⇒-[ ∧ₗₗ ]
    (·(A ∧ B) ⇒ (· A))   ⇒-[ ⟶ᵣ ]
    (∅ ⇒ ·((A ∧ B) ⟶ A)) ⇒-end

  --test2 : ∅ ⇒ ·(A ∨ (¬ A))

  test3 : ∅ ⇒ ·(((¬ ¬ A) ⟶ (¬ ¬ B)) ⟶ (¬ ¬(A ⟶ B)))
  test3{A = A}{B = B} =
    • (
      refl                                     ⇒-start
      ((· A)                  ⇒ (· A))          ⇒-[ weakenᵣ ]
      ((· A)                  ⇒ ((· A) ∪· B))   ⇒-[ permuteᵣ _permutes_.swap ]
      ((· A)                  ⇒ ((· B) ∪· A))   ⇒-[ ¬ₗ ]
      (((· A) ∪· (¬ A))       ⇒ (· B))          ⇒-[ permuteₗ _permutes_.swap ]
      ((·(¬ A) ∪· A)          ⇒ (· B))          ⇒-[ ⟶ᵣ ]
      (·(¬ A)                 ⇒ ·(A ⟶ B))       ⇒-[ ¬ₗ ]
      ((·(¬ A) ∪· ¬(A ⟶ B))   ⇒ ∅)              ⇒-[ permuteₗ _permutes_.swap ]
      ((·(¬(A ⟶ B)) ∪· (¬ A)) ⇒ ∅)              ⇒-[ ¬ᵣ ]
      (·(¬(A ⟶ B))            ⇒ (∅ ∪· (¬ ¬ A))) ⇒-end
    )
    • (
      refl ⇒-start
      ((· B)                    ⇒ (· B))    ⇒-[ weakenₗ ]
      (((· B) ∪· A)             ⇒ (· B))    ⇒-[ ⟶ᵣ ]
      ((· B)                    ⇒ ·(A ⟶ B)) ⇒-[ ¬ₗ ]
      (((· B) ∪· ¬(A ⟶ B))      ⇒ ∅)        ⇒-[ permuteₗ _permutes_.swap ]
      ((·(¬(A ⟶ B)) ∪· B)       ⇒ ∅)        ⇒-[ ¬ᵣ ]
      (·(¬(A ⟶ B))              ⇒ ·(¬ B))   ⇒-[ ¬ₗ ]
      ((·(¬(A ⟶ B)) ∪· (¬ ¬ B)) ⇒ ∅)        ⇒-end
    )
    ⇒₂-[ ⟶ₗ ]
    ((·(¬(A ⟶ B)) ∪· ((¬ ¬ A) ⟶ (¬ ¬ B))) ⇒ ∅)                                     ⇒-[ permuteₗ _permutes_.swap ]
    ((·((¬ ¬ A) ⟶ (¬ ¬ B)) ∪· ¬(A ⟶ B))   ⇒ ∅)                                     ⇒-[ ¬ᵣ ]
    (·((¬ ¬ A) ⟶ (¬ ¬ B))                 ⇒ ·(¬ ¬(A ⟶ B)))                         ⇒-[ ⟶ᵣ ]
    (∅                                    ⇒ ·(((¬ ¬ A) ⟶ (¬ ¬ B)) ⟶ (¬ ¬(A ⟶ B)))) ⇒-end

  test4 : (∅ ⇒ ·(((A ⟶ B) ⟶ A) ⟶ A))
  test4 {A = A}{B = B} =
    • (
      refl ⇒-start
      ((· A) ⇒ (· A))              ⇒-[ weakenᵣ ]
      ((· A) ⇒ ((· A) ∪· B))       ⇒-[ ⟶ᵣ ]
      (∅     ⇒ ((· A) ∪· (A ⟶ B))) ⇒-end
    )
    • ((· A) ⇒ (· A))              :-[ refl ]
    ⇒₂-[ ⟶ₗ ]
    ((∅ ∪· ((A ⟶ B) ⟶ A)) ⇒ (∅ ∪· A))             ⇒-[ ⟶ᵣ ]
    (∅                    ⇒ ·(((A ⟶ B) ⟶ A) ⟶ A)) ⇒-end

  -- ⟶ᵣ (¬ᵣ (permuteₗ _permutes_.swap (⟶ₗ (¬ᵣ (permuteₗ _permutes_.swap (¬ₗ (⟶ᵣ (permuteₗ _permutes_.swap (¬ₗ (permuteᵣ _permutes_.swap (weakenᵣ axiom)))))))) (¬ₗ (¬ᵣ (permuteₗ _permutes_.swap (¬ₗ (⟶ᵣ (weakenₗ axiom)))))))))

  {-
  [∧]-intro : ((Γ ∪· A ∪· B) ⇒ (Γ ∪· (A ∧ B)))
  [∧]-intro = ∧ᵣ ([⇒]-super skip) ([⇒]-super (p ↦ {!!}))

  [∧]-elimₗ : ((Γ ∪· (A ∧ B)) ⇒ (Γ ∪· A))
  [∧]-elimₗ = {!!}
  -}

  {-
  test : (Γ ⇒ Δ₁) → .(Δ₁ permutes Δ₂) → (Δ₂ ⇒ Δ₃) → (Γ ⇒ Δ₃)

  [∧]-intro : (Γ ⇒ ·(A)) → (Γ ⇒ ·(B)) → (Γ ⇒ ·(A ∧ B))
  [∧]-intro = ∧ᵣ

  [∧]-elimₗ : (Γ ⇒ Δ ∪· (A ∧ B)) → (Γ ⇒ (Δ ∪· A))
  [∧]-elimₗ axiom = ∧ₗₗ axiom
  [∧]-elimₗ (weakenₗ p) = weakenₗ ([∧]-elimₗ p)
  [∧]-elimₗ (permuteₗ x p) = permuteₗ x ([∧]-elimₗ p)
  [∧]-elimₗ (contractₗ p) = contractₗ ([∧]-elimₗ p)
  [∧]-elimₗ (∧ₗₗ p) = ∧ₗₗ ([∧]-elimₗ p)
  [∧]-elimₗ (∧ₗᵣ p) = ∧ₗᵣ ([∧]-elimₗ p)
  [∧]-elimₗ (∨ₗ p q) = ∨ₗ ([∧]-elimₗ p) ([∧]-elimₗ q)
  [∧]-elimₗ (⟶ₗ p q) = ⟶ₗ (permuteᵣ _permutes_.swap ([∧]-elimₗ(permuteᵣ _permutes_.swap p))) ([∧]-elimₗ q)
  [∧]-elimₗ (weakenᵣ p) = weakenᵣ p
  [∧]-elimₗ (permuteᵣ x p) = test p x {!!}
  [∧]-elimₗ (contractᵣ p) = contractᵣ([∧]-elimₗ(permuteᵣ _permutes_.swap ([∧]-elimₗ p)))
  [∧]-elimₗ (∧ᵣ p q) = p
  -}

  {-
  soundness : (Γ ⇒ Δ) → ((_∈ Γ) ⊨₊ (_∈ Δ))
  soundness axiom          𝔐Γ = 𝔐Γ
  soundness (weakenₗ p)    𝔐Γ = soundness p (𝔐Γ ∘ skip)
  soundness (permuteₗ x p) 𝔐Γ = {!!}
  soundness (contractₗ p)  𝔐Γ = {!!}
  soundness ⊥ₗ             𝔐Γ ()
  soundness (∧ₗₗ p) 𝔐Γ {elem} (use [≡]-intro) = soundness p (q ↦ 𝔐Γ {!!}) (use [≡]-intro)
  -- 𝔐Γ{elem} {!soundness p ? ?!}
  -- soundness p {!!} (use {!!})
  soundness (∧ₗₗ p) 𝔐Γ (skip q) = {!!}
  soundness (∧ₗᵣ p)        𝔐Γ = {!!}
  soundness (∨ₗ p q)       𝔐Γ = {!!}
  soundness (⟶ₗ p q)       𝔐Γ = soundness p (𝔐Γ ∘ skip) ∘ skip
  soundness (weakenᵣ p)    𝔐Γ = {!!}
  soundness (permuteᵣ x p) 𝔐Γ = {!!}
  soundness (contractᵣ p)  𝔐Γ = soundness p 𝔐Γ ∘ skip
  soundness (∧ᵣ p q)       𝔐Γ = {!!}
  soundness (∨ᵣₗ p)        𝔐Γ = {!!}
  soundness (∨ᵣᵣ p)        𝔐Γ = {!!}
  soundness (⟶ᵣ p)         𝔐Γ = {!!}
  -}

{-
  excluded-middle : Γ ⇒ (Δ ∪ ·(A ∨ (¬ A)))
  excluded-middle = ∨ᵣₗ {!!}

  soundness : (Γ ⇒ Δ) → (Γ ⊨₊ Δ)
  soundness axiom = id
  soundness (weakenₗ p) 𝔐Γ = soundness p (𝔐Γ ∘ Left)
  soundness (∧ₗₗ p) 𝔐Γ e = soundness p (\{(Left Γelem) → 𝔐Γ(Left Γelem) ; (Right [≡]-intro) → 𝔐Γ (Right {!!})}) e
  soundness (∧ₗᵣ p) 𝔐Γ e = soundness p (\{(Left Γelem) → 𝔐Γ (Left Γelem) ; (Right [≡]-intro) → 𝔐Γ (Right {!!})}) e
  soundness (∨ₗ p q) 𝔐Γ e = soundness p (\{(Left r) → 𝔐Γ (Left r) ; (Right r) → {!!}}) e
  soundness (⟶ₗ p q) 𝔐Γ = soundness p (𝔐Γ ∘ Left) ∘ Left
  soundness (weakenᵣ p) 𝔐Γ (Left Δelem)      = soundness p 𝔐Γ Δelem
  soundness (weakenᵣ p) 𝔐Γ (Right [≡]-intro) = {!!}
  soundness (∧ᵣ p q) 𝔐Γ (Left Δelem)      = soundness p 𝔐Γ (Left Δelem)
  soundness (∧ᵣ p q) 𝔐Γ (Right [≡]-intro) = Logic.[∧]-intro (soundness p 𝔐Γ (Right [≡]-intro)) (soundness q 𝔐Γ (Right [≡]-intro))
  soundness (∨ᵣₗ p) 𝔐Γ e = {!!}
  soundness (∨ᵣᵣ p) 𝔐Γ e = {!!}
  soundness (⟶ᵣ p) 𝔐Γ (Left x) = {!!}
  soundness (⟶ᵣ p) 𝔐Γ (Right [≡]-intro) = {!soundness p ? ?!}
-}


  module _ (cut : ∀{Γ₁ Γ₂ Δ₁ Δ₂}{φ} → (Γ₁ ⇒ (Δ₁ ∪· φ)) → ((Γ₂ ∪· φ) ⇒ Δ₂) → ((Γ₁ ∪ Γ₂) ⇒ (Δ₁ ∪ Δ₂))) where
    open import Formalization.ClassicalPropositionalLogic.NaturalDeduction

    open import Data.List.Relation.Quantification
    open import Functional.Instance
    open import Sets.PredicateSet as PredSet using (PredSet)
    open import Sets.PredicateSet.Listable
    open import Type.Properties.MereProposition

    ¬ᵣ-⊥ : ((Γ ∪· A) ⇒ (· ⊥)) → (Γ ⇒ (Δ ∪· (¬ A)))
    ¬ᵣ-⊥ {Γ = Γ}{A = A}{Δ = Δ} p = permute{Γ₁ = Γ ∪ Γ}{Γ₂ = Γ} {!!} {!!} (cut{Γ₁ = Γ}{Γ₂ = Γ}{Δ₁ = Δ}{Δ₂ = ·(¬ A)} {!!} {!!})

    from-naturalDeduction : ∀{Γ} ⦃ _ : Listable{ℓ}(Γ) ⦄ → (Γ ⊢ φ) → (list(Γ) ⇒ (· φ))
    to-naturalDeduction : (Γ ⇒ (· φ)) → ((_∈ Γ) ⊢ φ)

    from-naturalDeduction (direct x) = [⇒]-membership(Listable.proof infer x)
    from-naturalDeduction [⊤]-intro          = [⇒][++]ₗ-weakenₗ ⊤ᵣ
    from-naturalDeduction ([⊥]-intro  p q)   = {!!}
    from-naturalDeduction ([⊥]-elim   p)     = {!from-naturalDeduction p!}
    from-naturalDeduction {Γ = Γ} ([¬]-intro  p)     = {!(permuteₗ (list-[∪·] {Γ = Γ}) (from-naturalDeduction ⦃ ? ⦄ p))!}
    from-naturalDeduction ([¬]-elim   p)     = {!!}
    from-naturalDeduction ([∧]-intro  p q)   = ∧ᵣ (from-naturalDeduction p) (from-naturalDeduction q)
    from-naturalDeduction ([∧]-elimₗ  p)     = permute permₗ permᵣ (cut (from-naturalDeduction p) (∧ₗₗ refl)) where
      permₗ = sub₂(_≡ₑ_)(_permutes_) (identityᵣ(_∪_)(∅))
      permᵣ = sub₂(_≡ₑ_)(_permutes_) (identityₗ(_∪_)(∅))
    from-naturalDeduction ([∧]-elimᵣ  p)     = permute permₗ permᵣ (cut (from-naturalDeduction p) (∧ₗᵣ refl)) where
      permₗ = sub₂(_≡ₑ_)(_permutes_) (identityᵣ(_∪_)(∅))
      permᵣ = sub₂(_≡ₑ_)(_permutes_) (identityₗ(_∪_)(∅))
    from-naturalDeduction ([∨]-introₗ p)     = ∨ᵣₗ (from-naturalDeduction p)
    from-naturalDeduction ([∨]-introᵣ p)     = ∨ᵣᵣ (from-naturalDeduction p)
    from-naturalDeduction ([∨]-elim   p q r) = {!!}
    from-naturalDeduction {Γ = Γ} ([⟶]-intro  p)     = ⟶ᵣ (permuteₗ (list-[∪·] {S = Γ}) (from-naturalDeduction ⦃ {!!} ⦄ p))
    from-naturalDeduction ([⟶]-elim   p q)   = {!!} -- permute {!!} {!!} (cut (from-naturalDeduction p) {!cut (from-naturalDeduction q) ?!})
    from-naturalDeduction ([⟷]-intro  p q)   = {!!}
    from-naturalDeduction ([⟷]-elimₗ  p q)   = {!!}
    from-naturalDeduction ([⟷]-elimᵣ  p q)   = {!!}

    {-
    from-naturalDeduction : ((_∈ Γ) ⊢ φ) → (Γ ⇒ (· φ))
    from-naturalDeduction (direct (use {x = x}{l = l} [≡]-intro)) = [⇒][++]ₗ-weakenₗ {Γ₁ = · x}{Γ₂ = l} axiom
    from-naturalDeduction (direct (skip x)) = weakenₗ(from-naturalDeduction (direct x))
    from-naturalDeduction [⊤]-intro = [⇒][++]ₗ-weakenₗ ⊤ᵣ
    from-naturalDeduction ([⊥]-intro p q) = {!!}
    from-naturalDeduction ([⊥]-elim p) = {!!}
    from-naturalDeduction ([¬]-intro p) = {!!}
    from-naturalDeduction ([¬]-elim p) = {!!}
    from-naturalDeduction ([∧]-intro p q) = ∧ᵣ (from-naturalDeduction p) (from-naturalDeduction q)
    from-naturalDeduction ([∧]-elimₗ p) = permute permₗ permᵣ (cut (from-naturalDeduction p) (∧ₗₗ axiom)) where
      permₗ = sub₂(_≡ₑ_)(_permutes_) (identityᵣ(_∪_)(∅))
      permᵣ = sub₂(_≡ₑ_)(_permutes_) (identityₗ(_∪_)(∅))
    from-naturalDeduction ([∧]-elimᵣ p) = permute permₗ permᵣ (cut (from-naturalDeduction p) (∧ₗᵣ axiom)) where
      permₗ = sub₂(_≡ₑ_)(_permutes_) (identityᵣ(_∪_)(∅))
      permᵣ = sub₂(_≡ₑ_)(_permutes_) (identityₗ(_∪_)(∅))
    from-naturalDeduction ([∨]-introₗ p) = ∨ᵣₗ (from-naturalDeduction p)
    from-naturalDeduction ([∨]-introᵣ p) = ∨ᵣᵣ (from-naturalDeduction p)
    from-naturalDeduction ([∨]-elim p q r) = {!!}
    from-naturalDeduction ([⟶]-intro p) = ⟶ᵣ {!from-naturalDeduction p!}
    from-naturalDeduction ([⟶]-elim p q) = {!!}
    from-naturalDeduction ([⟷]-intro p q) = {!!}
    from-naturalDeduction ([⟷]-elimₗ p q) = {!!}
    from-naturalDeduction ([⟷]-elimᵣ p q) = {!!}
    -}

{-    to-naturalDeduction axiom = direct (use [≡]-intro)
    to-naturalDeduction (weakenₗ p) = {!!}
    to-naturalDeduction (permuteₗ x p) = {!!}
    to-naturalDeduction (contractₗ p) = {!!}
    to-naturalDeduction (∧ₗₗ p) = {!!}
    to-naturalDeduction (∧ₗᵣ p) = {!!}
    to-naturalDeduction (∨ₗ p p₁) = {!!}
    to-naturalDeduction (⟶ₗ p p₁) = {!!}
    to-naturalDeduction (weakenᵣ p) = {!!}
    to-naturalDeduction (permuteᵣ x p) = {!!}
    to-naturalDeduction (contractᵣ p) = {!!}
    to-naturalDeduction (∧ᵣ p p₁) = [∧]-intro (to-naturalDeduction p) (to-naturalDeduction p₁)
    to-naturalDeduction (∨ᵣₗ p) = [∨]-introₗ (to-naturalDeduction p)
    to-naturalDeduction (∨ᵣᵣ p) = [∨]-introᵣ (to-naturalDeduction p)
    to-naturalDeduction (⟶ᵣ p) = [⟶]-intro {!to-naturalDeduction p!}
-}

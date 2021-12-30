open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Minimal.NaturalDeduction.NegativeTranslations (𝔏 : Signature) where
open Signature(𝔏)

open import Data.Either as Either using (Left ; Right)
open import Data.ListSized using (List)
import      Logic.Propositional as Meta
import      Logic.Predicate as Meta
import      Lvl
open import Formalization.PredicateLogic.Minimal.NaturalDeduction (𝔏)
import      Formalization.PredicateLogic.Classical.NaturalDeduction
private module Classical = Formalization.PredicateLogic.Classical.NaturalDeduction (𝔏)
open import Formalization.PredicateLogic.Syntax(𝔏)
open import Formalization.PredicateLogic.Syntax.NegativeTranslations(𝔏)
open import Formalization.PredicateLogic.Syntax.Substitution(𝔏)
open import Functional using (_∘_ ; _∘₂_ ; _∘₃_ ; _∘₄_ ; swap ; _←_)
open import Numeral.Finite
open import Numeral.Natural
open import Relator.Equals
open import Relator.Equals.Proofs.Equiv
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _∪•_ ; _∖_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇] ; map ; unmap) renaming (•_ to · ; _≡_ to _≡ₛ_)
open import Structure.Relator
open import Type

-- TODO: Move this module
module _ where
  private variable ℓ : Lvl.Level
  private variable T A B : Type{ℓ}
  private variable S S₁ S₂ : PredSet{ℓ}(T)
  private variable f : A → B
  private variable x : T

  postulate map-preserves-union : (map f(S₁ ∪ S₂) ⊆ ((map f(S₁)) ∪ (map f(S₂))))

  postulate map-preserves-singleton : (map f(S₁ ∪ S₂) ⊆ ((map f(S₁)) ∪ (map f(S₂))))

  postulate map-preserves-union-singleton : (map f(S ∪ · x) ⊆ ((map f(S)) ∪ ·(f(x))))

private variable ℓ ℓ₁ ℓ₂ : Lvl.Level
private variable args n vars : ℕ
private variable Γ Γ₁ Γ₂ : PredSet{ℓ}(Formula(vars))
private variable φ ψ γ φ₁ ψ₁ γ₁ φ₂ ψ₂ γ₂ φ₃ ψ₃ φ₄ ψ₄ φ₅ ψ₅ δ₁ δ₂ : Formula(vars)
private variable p : Prop(args)
private variable x : List(Term(vars))(args)

[⊢]-functionₗ : (Γ₁ ≡ₛ Γ₂) → ((Γ₁ ⊢_) ≡ₛ (Γ₂ ⊢_))
[⊢]-functionₗ Γ₁Γ₂ = Meta.[↔]-intro (weaken (Meta.[↔]-to-[←] Γ₁Γ₂)) (weaken (Meta.[↔]-to-[→] Γ₁Γ₂))

[⊢][→]-elim : ((Γ ∪ · φ) ⊢ ψ) → ((Γ ⊢ φ) → (Γ ⊢ ψ))
[⊢][→]-elim Γφψ Γφ = [∨]-elim Γφψ Γφψ ([∨]-introₗ Γφ)

[⟶]-intro-inverse : (Γ ⊢ (φ ⟶ ψ)) → ((Γ ∪ · φ) ⊢ ψ)
[⟶]-intro-inverse p = [⟶]-elim (direct (Right [≡]-intro)) (weaken-union p)

weaken-closure-union : (((Γ₁ ⊢_) ∪ Γ₂) ⊢ φ) → ((((Γ₁ ∪ Γ₂) ⊢_)) ⊢ φ)
weaken-closure-union {Γ₁ = Γ₁}{Γ₂ = Γ₂}{φ = φ} = weaken sub where
  sub : ((Γ₁ ⊢_) ∪ Γ₂) ⊆ ((Γ₁ ∪ Γ₂) ⊢_)
  sub (Left  p) = weaken-union p
  sub (Right p) = direct (Right p)

{-
assume-closure : ((Γ ⊢_) ⊢ φ) → (Γ ⊢ φ)
assume-closure (direct     p)     = p
assume-closure [⊤]-intro          = [⊤]-intro
assume-closure ([∧]-intro  p q)   = [∧]-intro (assume-closure p) (assume-closure q)
assume-closure ([∧]-elimₗ  p)     = [∧]-elimₗ (assume-closure p)
assume-closure ([∧]-elimᵣ  p)     = [∧]-elimᵣ (assume-closure p)
assume-closure ([∨]-introₗ p)     = [∨]-introₗ (assume-closure p)
assume-closure ([∨]-introᵣ p)     = [∨]-introᵣ (assume-closure p)
assume-closure ([∨]-elim   p q r) = [∨]-elim {!assume-closure(weaken-closure-union p)!} ([⟶]-elim (direct(Right [≡]-intro)) {!!}) (assume-closure r)
assume-closure ([⟶]-intro  p)     = [⟶]-intro (assume-closure {!weaken-closure-union p!})
assume-closure ([⟶]-elim   p q)   = [⟶]-elim (assume-closure p) (assume-closure q)
assume-closure ([Ɐ]-intro  p)     = [Ɐ]-intro (assume-closure p)
assume-closure ([Ɐ]-elim   p)     = [Ɐ]-elim (assume-closure p)
assume-closure ([∃]-intro  p)     = [∃]-intro (assume-closure p)
assume-closure ([∃]-elim   p q)   = [∃]-elim (assume-closure {!!}) (assume-closure q)
-}

-- 2.1.8B1
[¬¬]-intro-[⟶] : (Γ ⊢ (φ ⟶ (¬¬ φ)))
[¬¬]-intro-[⟶] = [⟶]-intro ([¬¬]-intro (direct (Right [≡]-intro)))

-- 2.1.8.A1
[⟶]-const : Γ ⊢ (φ ⟶ ψ ⟶ φ)
[⟶]-const = [⟶]-intro ([⟶]-intro (direct (Left (Right [≡]-intro))))

[⟶]-refl : Γ ⊢ (φ ⟶ φ)
[⟶]-refl = [⟶]-intro (direct (Right [≡]-intro))

[⟷]-refl : Γ ⊢ (φ ⟷ φ)
[⟷]-refl = [⟷]-intro (direct (Right [≡]-intro)) (direct (Right [≡]-intro))

[⟶]-trans : (Γ ⊢ ((φ ⟶ ψ) ⟶ (ψ ⟶ γ) ⟶ (φ ⟶ γ)))
[⟶]-trans = [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim ([⟶]-elim (direct (Right [≡]-intro)) (direct (Left (Left (Right [≡]-intro))))) (direct (Left (Right [≡]-intro))))))

[⟶]-contrapositiveᵣ : (Γ ⊢ (φ ⟶ ψ) ⟶ ((¬ φ) ⟵ (¬ ψ)))
[⟶]-contrapositiveᵣ = [⟶]-trans

[⟶]-double-contrapositiveᵣ : (Γ ⊢ (φ ⟶ ψ) ⟶ ((¬¬ φ) ⟶ (¬¬ ψ)))
[⟶]-double-contrapositiveᵣ = [⟶]-intro ([⟶]-elim ([⟶]-elim (direct (Right [≡]-intro)) [⟶]-contrapositiveᵣ) [⟶]-contrapositiveᵣ)

[⟶]-elim₂ : (Γ ⊢ φ₁) → (Γ ⊢ φ₂) → (Γ ⊢ (φ₁ ⟶ φ₂ ⟶ ψ)) → (Γ ⊢ ψ)
[⟶]-elim₂ = swap(_∘_) [⟶]-elim ∘ (swap(_∘_) ∘ [⟶]-elim)

[⟶]-elim₃ : (Γ ⊢ φ₁) → (Γ ⊢ φ₂) → (Γ ⊢ φ₃) → (Γ ⊢ (φ₁ ⟶ φ₂ ⟶ φ₃ ⟶ ψ)) → (Γ ⊢ ψ)
[⟶]-elim₃ = swap(_∘_) [⟶]-elim ∘₂ (swap(_∘_) ∘₂ [⟶]-elim₂)

[⟶]-elim₄ : (Γ ⊢ φ₁) → (Γ ⊢ φ₂) → (Γ ⊢ φ₃) → (Γ ⊢ φ₄) → (Γ ⊢ (φ₁ ⟶ φ₂ ⟶ φ₃ ⟶ φ₄ ⟶ ψ)) → (Γ ⊢ ψ)
[⟶]-elim₄ = swap(_∘_) [⟶]-elim ∘₃ (swap(_∘_) ∘₃ [⟶]-elim₃)

[⟶]-elim₅ : (Γ ⊢ φ₁) → (Γ ⊢ φ₂) → (Γ ⊢ φ₃) → (Γ ⊢ φ₄) → (Γ ⊢ φ₅) → (Γ ⊢ (φ₁ ⟶ φ₂ ⟶ φ₃ ⟶ φ₄ ⟶ φ₅ ⟶ ψ)) → (Γ ⊢ ψ)
[⟶]-elim₅ = swap(_∘_) [⟶]-elim ∘₄ (swap(_∘_) ∘₄ [⟶]-elim₄)

-- 2.1.8B2
[¬¬¬]-elim : Γ ⊢ ((¬ ¬ ¬ φ) ⟶ (¬ φ))
[¬¬¬]-elim = [⟶]-intro ([⟶]-intro ([⟶]-elim ([¬¬]-intro (direct (Right [≡]-intro))) (direct (Left (Right [≡]-intro)))))

[∨]-introₗ-by-[¬∧] : Γ ⊢ ((¬ φ) ⟶ ¬(φ ∧ ψ))
[∨]-introₗ-by-[¬∧] = [⟶]-intro ([⟶]-intro ([⟶]-elim ([∧]-elimₗ (direct (Right [≡]-intro))) (direct (Left (Right [≡]-intro)))))

[∨]-introᵣ-by-[¬∧] : Γ ⊢ ((¬ ψ) ⟶ ¬(φ ∧ ψ))
[∨]-introᵣ-by-[¬∧] = [⟶]-intro ([⟶]-intro ([⟶]-elim ([∧]-elimᵣ (direct (Right [≡]-intro))) (direct (Left (Right [≡]-intro)))))

[∨]-introₗ-by-[¬¬∧¬] : Γ ⊢ (φ ⟶ ¬((¬ φ) ∧ (¬ ψ)))
[∨]-introₗ-by-[¬¬∧¬] = [⟶]-intro ([⟶]-intro ([⟶]-elim (direct (Left (Right [≡]-intro))) ([∧]-elimₗ (direct (Right [≡]-intro)))))

[∨]-introᵣ-by-[¬¬∧¬] : Γ ⊢ (ψ ⟶ ¬((¬ φ) ∧ (¬ ψ)))
[∨]-introᵣ-by-[¬¬∧¬] = [⟶]-intro ([⟶]-intro ([⟶]-elim (direct (Left (Right [≡]-intro))) ([∧]-elimᵣ (direct (Right [≡]-intro)))))

[∃]-intro-by-[¬Ɐ] : ∀{t} → (Γ ⊢ ((¬(substitute0 t φ)) ⟶ ¬(Ɐ φ)))
[∃]-intro-by-[¬Ɐ] = [⟶]-intro ([⟶]-intro ([⟶]-elim ([Ɐ]-elim (direct (Right [≡]-intro))) (direct (Left (Right [≡]-intro)))))

[∃]-intro-by-[¬Ɐ¬] : ∀{t} → (Γ ⊢ ((substitute0 t φ) ⟶ ¬(Ɐ(¬ φ))))
[∃]-intro-by-[¬Ɐ¬] = [⟶]-intro ([⟶]-intro ([⟶]-elim (direct (Left (Right [≡]-intro))) ([Ɐ]-elim (direct (Right [≡]-intro)))))

[∧]-map : Γ ⊢ ((φ₁ ⟶ φ₂) ⟶ (ψ₁ ⟶ ψ₂) ⟶ ((φ₁ ∧ ψ₁) ⟶ (φ₂ ∧ ψ₂)))
[∧]-map = [⟶]-intro ([⟶]-intro ([⟶]-intro ([∧]-intro ([⟶]-elim ([∧]-elimₗ (direct (Right [≡]-intro))) (direct (Left (Left (Right [≡]-intro))))) ([⟶]-elim ([∧]-elimᵣ (direct (Right [≡]-intro))) (direct (Left (Right [≡]-intro)))))))

[∨]-map : Γ ⊢ ((φ₁ ⟶ φ₂) ⟶ (ψ₁ ⟶ ψ₂) ⟶ ((φ₁ ∨ ψ₁) ⟶ (φ₂ ∨ ψ₂)))
[∨]-map = [⟶]-intro ([⟶]-intro ([⟶]-intro ([∨]-elim ([∨]-introₗ ([⟶]-intro-inverse (direct (Left (Left (Right [≡]-intro)))))) ([∨]-introᵣ ([⟶]-intro-inverse (direct (Left (Right [≡]-intro))))) (direct (Right [≡]-intro)))))

[Ɐ]-map : Γ ⊢ (Ɐ(φ₁ ⟶ φ₂) ⟶ ((Ɐ φ₁) ⟶ (Ɐ φ₂)))
[Ɐ]-map = [⟶]-intro ([⟶]-intro ([Ɐ]-intro ([⟶]-elim ([Ɐ]-elim (direct (Right [≡]-intro))) ([Ɐ]-elim(direct (Left (Right [≡]-intro)))))))

[⟶]-map : Γ ⊢ ((φ₁ ⟵ φ₂) ⟶ (ψ₁ ⟶ ψ₂) ⟶ ((φ₁ ⟶ ψ₁) ⟶ (φ₂ ⟶ ψ₂)))
[⟶]-map = [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim ([⟶]-elim ([⟶]-elim (direct (Right [≡]-intro)) (direct (Left (Left (Left (Right [≡]-intro)))))) (direct (Left (Right [≡]-intro)))) (direct (Left (Left (Right [≡]-intro))))))))

[⟶]-map₂ : Γ ⊢ ((φ₁ ⟵ φ₂) ⟶ (ψ₁ ⟵ ψ₂) ⟶ (γ₁ ⟶ γ₂) ⟶ ((φ₁ ⟶ ψ₁ ⟶ γ₁) ⟶ (φ₂ ⟶ ψ₂ ⟶ γ₂)))
[⟶]-map₂ = [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim₂ (direct (Left (Left (Right [≡]-intro)))) ([⟶]-elim₂ (direct (Left (Right [≡]-intro))) (direct (Right [≡]-intro)) [⟶]-map) [⟶]-map)))

[⟶]-map₃ : Γ ⊢ ((φ₁ ⟵ φ₂) ⟶ (ψ₁ ⟵ ψ₂) ⟶ (γ₁ ⟵ γ₂) ⟶ (δ₁ ⟶ δ₂) ⟶ ((φ₁ ⟶ ψ₁ ⟶ γ₁ ⟶ δ₁) ⟶ (φ₂ ⟶ ψ₂ ⟶ γ₂ ⟶ δ₂)))
[⟶]-map₃ = [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim₃ (direct (Left (Left (Left (Right [≡]-intro))))) (direct (Left (Left (Right [≡]-intro)))) ([⟶]-elim₂ (direct (Left (Right [≡]-intro))) (direct (Right [≡]-intro)) [⟶]-map) [⟶]-map₂))))

[¬]-map : Γ ⊢ ((φ ⟵ ψ) ⟶ (¬ φ) ⟶ (¬ ψ))
[¬]-map = [⟶]-contrapositiveᵣ

[⟶]-trans₂ : (Γ ⊢ ((φ₁ ⟶ φ₂ ⟶ ψ) ⟶ (ψ ⟶ γ) ⟶ (φ₁ ⟶ φ₂ ⟶ γ)))
[⟶]-trans₂ = [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim ([⟶]-elim₂ (direct (Left (Right [≡]-intro))) (direct (Right [≡]-intro)) (direct (Left (Left (Left (Right [≡]-intro)))))) (direct (Left (Left (Right [≡]-intro))))))))

-- 2.1.8B3
[¬¬]-preserve-[⟶] : Γ ⊢ (¬¬(φ ⟶ ψ) ⟶ ((¬¬ φ) ⟶ (¬¬ ψ)))
[¬¬]-preserve-[⟶] = [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim ([⟶]-intro ([⟶]-elim ([⟶]-elim (direct (Left (Left (Right [≡]-intro)))) ([⟶]-elim (direct(Right [≡]-intro)) [⟶]-double-contrapositiveᵣ)) ([¬¬]-intro (direct (Left (Right [≡]-intro)))))) (direct (Left (Left (Right [≡]-intro)))))))

-- 2.1.8B4
[¬¬]-preserve-[∧] : Γ ⊢ (¬¬(φ ∧ ψ) ⟷ ((¬¬ φ) ∧ (¬¬ ψ)))
[¬¬]-preserve-[∧] {Γ = Γ}{φ = φ} =
  [⟷]-intro
    ([⟶]-intro ([⟶]-elim ([⟶]-intro ([⟶]-elim ([⟶]-intro ([⟶]-elim ([∧]-intro (direct (Left (Right [≡]-intro))) (direct (Right [≡]-intro))) (direct (Left (Left (Right [≡]-intro)))))) ([∧]-elimᵣ (direct (Left (Left (Right [≡]-intro))))))) ([∧]-elimₗ (direct (Left (Right [≡]-intro))))))
    ([∧]-intro
      ([⟶]-intro ([⟶]-elim ([⟶]-elim (direct (Right [≡]-intro)) [∨]-introₗ-by-[¬∧]) (direct (Left (Right [≡]-intro)))))
      ([⟶]-intro ([⟶]-elim ([⟶]-elim (direct (Right [≡]-intro)) [∨]-introᵣ-by-[¬∧]) (direct (Left (Right [≡]-intro)))))
    )

-- 2.1.8B5
[¬]-preserve-[∨][∧] : Γ ⊢ (¬(φ ∨ ψ) ⟷ ((¬ φ) ∧ (¬ ψ)))
[¬]-preserve-[∨][∧] =
  [⟷]-intro
    ([⟶]-intro ([∨]-elim
      ([⟶]-elim (direct (Right [≡]-intro)) ([∧]-elimₗ (direct (Left (Left (Right [≡]-intro))))))
      ([⟶]-elim (direct (Right [≡]-intro)) ([∧]-elimᵣ (direct (Left (Left (Right [≡]-intro))))))
      (direct (Right [≡]-intro))
    ))
    ([∧]-intro
      ([⟶]-intro ([⟶]-elim ([∨]-introₗ (direct (Right [≡]-intro))) (direct (Left (Right [≡]-intro)))))
      ([⟶]-intro ([⟶]-elim ([∨]-introᵣ (direct (Right [≡]-intro))) (direct (Left (Right [≡]-intro)))))
    )

-- 2.1.8B6
[¬¬]-preserve-[Ɐ] : Γ ⊢ (¬¬(Ɐ φ) ⟶ (Ɐ(¬¬ φ)))
[¬¬]-preserve-[Ɐ] = [⟶]-intro ([Ɐ]-intro ([⟶]-intro ([⟶]-elim ([⟶]-elim (direct (Right [≡]-intro)) [∃]-intro-by-[¬Ɐ]) (direct (Left (Right [≡]-intro))))))

[¬]-preserve-[∃][Ɐ] : Γ ⊢ (¬(∃ φ) ⟷ (Ɐ(¬ φ)))
[¬]-preserve-[∃][Ɐ] =
  [⟷]-intro
    ([⟶]-intro ([∃]-elim ([⟶]-intro-inverse ([Ɐ]-elim (direct (Left (Right [≡]-intro))))) (direct (Right [≡]-intro))))
    ([Ɐ]-intro ([⟶]-intro ([⟶]-elim ([∃]-intro (direct (Right [≡]-intro))) (direct (Left (Right [≡]-intro))))))

open import Functional.Instance

-- 2.3.1
data NegativeFragment : Formula(vars) → Type{ℓₚ Lvl.⊔ ℓₒ} where
  atom   : NegativeFragment(¬(p $ x))
  bottom : NegativeFragment{vars}(⊥)
  top    : NegativeFragment{vars}(⊤)
  and    : NegativeFragment(φ) → NegativeFragment(ψ) → NegativeFragment(φ ∧ ψ)
  impl   : NegativeFragment(φ) → NegativeFragment(ψ) → NegativeFragment(φ ⟶ ψ)
  all    : (∀{t} → NegativeFragment(substitute0 t φ)) → NegativeFragment(Ɐ φ)
pattern neg p = NegativeFragment.impl p bottom
instance _ = \{vars} {p}{args}{x} → atom{vars}{p = p}{args}{x = x}
instance _ = \{vars} → bottom{vars}
instance _ = \{vars} → top{vars}
instance _ = \{vars} {φ} ⦃ neg-φ ⦄ {ψ} ⦃ neg-ψ ⦄ → and{vars}{φ = φ}{ψ = ψ} neg-φ neg-ψ
instance _ = \{vars} {φ} ⦃ neg-φ ⦄ {ψ} ⦃ neg-ψ ⦄ → impl{vars}{φ = φ}{ψ = ψ} neg-φ neg-ψ
instance _ = \{vars} {φ} ⦃ neg-φ : ∀{_} → _ ⦄ → all{vars}{φ = φ} (\{t} → neg-φ{t})

-- 2.3.2
[¬¬]-elim-on-negativeFragment : NegativeFragment(φ) → (Γ ⊢ ((¬¬ φ) ⟶ φ))
[¬¬]-elim-on-negativeFragment atom             = [¬¬¬]-elim
[¬¬]-elim-on-negativeFragment bottom           = [¬¬]-intro [⟶]-refl
[¬¬]-elim-on-negativeFragment top              = [⟶]-intro [⊤]-intro
[¬¬]-elim-on-negativeFragment (and  negφ negψ) =
  [⟶]-intro ([∧]-intro
    ([⟶]-elim ([∧]-elimₗ([⟷]-elimᵣ (direct (Right [≡]-intro)) [¬¬]-preserve-[∧])) ([¬¬]-elim-on-negativeFragment negφ))
    ([⟶]-elim ([∧]-elimᵣ([⟷]-elimᵣ (direct (Right [≡]-intro)) [¬¬]-preserve-[∧])) ([¬¬]-elim-on-negativeFragment negψ))
  )
[¬¬]-elim-on-negativeFragment (impl negφ negψ) =
  [⟶]-intro ([⟶]-intro ([⟶]-elim
    ([⟶]-elim₂ (direct (Left (Right [≡]-intro))) ([¬¬]-intro (direct (Right [≡]-intro))) [¬¬]-preserve-[⟶])
    ([¬¬]-elim-on-negativeFragment negψ)
  ))
[¬¬]-elim-on-negativeFragment (all  negφ)      = [⟶]-intro ([Ɐ]-intro ([⟶]-elim ([⟶]-intro ([⟶]-elim ([⟶]-elim (direct (Right [≡]-intro)) [∃]-intro-by-[¬Ɐ]) (direct (Left (Right [≡]-intro))))) ([¬¬]-elim-on-negativeFragment negφ)))

Stable : ∀{ℓ}{vars} → Formula(vars) → Type
Stable{ℓ = ℓ} (φ) = ∀{Γ : PredSet{ℓ}(_)} → (Γ ⊢ (¬¬ φ ⟶ φ))

[¬]-stability : Stable{ℓ}(¬ φ)
[¬]-stability = [¬¬¬]-elim

-- [∨]-stability : Stable(φ) → Stable(ψ) → Stable{ℓ}(φ ∨ ψ)
-- [∨]-stability sφ sψ = [⟶]-intro ([∨]-elim ([∨]-introₗ {!!}) ([∨]-introᵣ {!!}) {!!})

[∨]-elim-by-[¬∧] : Stable(φ) → Stable(ψ) → Stable(γ) → (Γ ⊢ (((¬ φ) ⟶ γ) ⟶ ((¬ ψ) ⟶ γ) ⟶ ¬(φ ∧ ψ) ⟶ γ))
[∨]-elim-by-[¬∧] negφ negψ negγ = [⟶]-intro ([⟶]-intro ([⟶]-intro ([⟶]-elim ([⟶]-intro ([⟶]-elim ([⟶]-elim₃ negφ negψ ([∧]-intro ([⟶]-elim (direct (Right [≡]-intro)) ([⟶]-elim (direct (Left (Left (Left (Right [≡]-intro))))) [⟶]-contrapositiveᵣ)) ([⟶]-elim (direct (Right [≡]-intro)) ([⟶]-elim (direct (Left (Left (Right [≡]-intro)))) [⟶]-contrapositiveᵣ))) [∧]-map) (direct (Left (Right [≡]-intro))))) negγ)))

[∨]-elim-by-[¬¬∧¬] : (∀{ℓ} → Stable{ℓ}(γ)) → (Γ ⊢ ((φ ⟶ γ) ⟶ (ψ ⟶ γ) ⟶ ¬((¬ φ) ∧ (¬ ψ)) ⟶ γ))
[∨]-elim-by-[¬¬∧¬] negγ = [⟶]-elim₅ (pp negγ) (pp negγ) [⟶]-refl [⟶]-refl ([∨]-elim-by-[¬∧] [¬]-stability [¬]-stability negγ) [⟶]-map₃ where
  pp : Stable(ψ) → (Γ ⊢ ((φ ⟶ ψ) ⟶ ((¬¬ φ) ⟶ ψ)))
  pp negψ = [⟶]-elim₂ [⟶]-double-contrapositiveᵣ negψ [⟶]-trans₂

[⟷]-to-[⟵] : (Γ ⊢ (φ ⟷ ψ)) → (Γ ⊢ (φ ⟵ ψ))
[⟷]-to-[⟵] p = [⟶]-intro ([⟷]-elimₗ (direct (Right [≡]-intro)) (weaken-union p))

[⟷]-to-[⟶] : (Γ ⊢ (φ ⟷ ψ)) → (Γ ⊢ (φ ⟶ ψ))
[⟷]-to-[⟶] p = [⟶]-intro ([⟷]-elimᵣ (direct (Right [≡]-intro)) (weaken-union p))

[Ɐ][→]-distributivity : Γ ⊢ (Ɐ(φ ⟶ ψ) ⟶ (Ɐ φ) ⟶ (Ɐ ψ))
[Ɐ][→]-distributivity = [⟶]-intro ([⟶]-intro ([Ɐ]-intro ([⟶]-elim ([Ɐ]-elim (direct (Right [≡]-intro))) ([Ɐ]-elim (direct (Left (Right [≡]-intro)))))))

[¬∃]-to-[∀¬] : Γ ⊢ (¬(∃ φ) ⟶ Ɐ(¬ φ))
[¬∃]-to-[∀¬] = [⟶]-intro ([Ɐ]-intro ([⟶]-intro ([⟶]-elim ([∃]-intro (direct (Right [≡]-intro))) (direct (Left (Right [≡]-intro))))))

[¬Ɐ]-to-[∃¬] : (∀{t} → Stable(substitute0 t φ)) → Stable(∃(¬ φ)) → (Γ ⊢ (¬(Ɐ φ) ⟶ ∃(¬ φ)))
[¬Ɐ]-to-[∃¬] negφ nege = [⟶]-intro ([⟶]-elim ([⟶]-intro ([⟶]-elim ([⟶]-elim₂ ([Ɐ]-intro negφ) ([⟶]-elim (direct (Right [≡]-intro)) [¬∃]-to-[∀¬]) [Ɐ][→]-distributivity) (direct (Left (Right [≡]-intro))))) nege)

{-
test : (Γ ⊢ (¬¬ φ ⟶ φ)) → (Γ ⊢ (¬ Ɐ(¬ φ))) → (Γ ⊢ ∃ φ)
test negφ p = [∃]-elim ([∃]-intro {![⟶]-intro negφ!}) ([⟶]-elim p test2)
-}

[∃]-elim-by-[¬¬∧¬] : (∀{t} → (Γ ∪ ·(substitute0 t φ)) ⊢ ψ) → (Γ ⊢ ¬(Ɐ(¬ φ))) → (Γ ⊢ ψ)
[∃]-elim-by-[¬¬∧¬] p q = [∃]-elim p {!!}

-- test : ∀{t} → (Γ₁ ≡ₛ Γ₂) → (Γ₁ ⊢ φ) → (Γ₂ ⊢ substitute0 t φ)
-- test p = {!p!}

{-
test : ∀{t} → (∀{Γ : PredSet{ℓ}(Formula(𝐒(vars)))} → (Γ ⊢ φ)) → (∀{Γ : PredSet{ℓ}(Formula(vars))} → (Γ ⊢ substitute0 t φ))
test {t = t} Γφ {Γ} with Γφ{unmap(substitute0 t) Γ}
... | direct     p     = direct p
... | [⊤]-intro        = [⊤]-intro
... | [∧]-intro  p q   = [∧]-intro {!test p!} {!!}
... | [∧]-elimₗ  p     = {!!}
... | [∧]-elimᵣ  p     = {!!}
... | [∨]-introₗ p     = {!!}
... | [∨]-introᵣ p     = {!!}
... | [∨]-elim   p q r = {!!}
... | [⟶]-intro  p     = {!!}
... | [⟶]-elim   p q   = {!!}
... | [Ɐ]-intro  p     = {!!}
... | [Ɐ]-elim   p     = {!!}
... | [∃]-intro  p     = {!!}
... | [∃]-elim   p q   = {!!}
-}

substitute0-negativeFragment : NegativeFragment(φ) → ∀{t} → NegativeFragment(substitute0 t φ)
substitute0-negativeFragment atom       = atom
substitute0-negativeFragment bottom     = bottom
substitute0-negativeFragment top        = top
substitute0-negativeFragment (and  p q) = and (substitute0-negativeFragment p) (substitute0-negativeFragment q)
substitute0-negativeFragment (impl p q) = impl (substitute0-negativeFragment p) (substitute0-negativeFragment q)
substitute0-negativeFragment (all  p)   = {!!} -- all (substitute0-negativeFragment p)

ggTrans-negativeFragment : NegativeFragment(ggTrans(φ))
ggTrans-negativeFragment {φ = p $ x} = neg atom
ggTrans-negativeFragment {φ = ⊤}     = top
ggTrans-negativeFragment {φ = ⊥}     = bottom
ggTrans-negativeFragment {φ = φ ∧ ψ} = and ggTrans-negativeFragment ggTrans-negativeFragment
ggTrans-negativeFragment {φ = φ ∨ ψ} = neg(and(neg ggTrans-negativeFragment) (neg ggTrans-negativeFragment))
ggTrans-negativeFragment {φ = φ ⟶ ψ} = impl ggTrans-negativeFragment ggTrans-negativeFragment
ggTrans-negativeFragment {φ = Ɐ φ}   = all (substitute0-negativeFragment (ggTrans-negativeFragment {φ = φ}))
ggTrans-negativeFragment {φ = ∃ φ}   = neg (all (neg (substitute0-negativeFragment (ggTrans-negativeFragment {φ = φ}))))

-- [¬¬]-elim-of-koTrans : (Γ ⊢ (¬¬ ggTrans(φ))) ← (Γ ⊢ (ggTrans φ))

ggTrans-substitute0 : ∀{t} → (ggTrans(substitute0 t φ) ≡ substitute0 t (ggTrans φ))
ggTrans-substitute0 {φ = P $ x} = [≡]-intro
ggTrans-substitute0 {φ = ⊤}     = [≡]-intro
ggTrans-substitute0 {φ = ⊥}     = [≡]-intro
ggTrans-substitute0 {φ = φ ∧ ψ}{t}
  rewrite ggTrans-substitute0 {φ = φ}{t}
  rewrite ggTrans-substitute0 {φ = ψ}{t}
  = [≡]-intro
ggTrans-substitute0 {φ = φ ∨ ψ}{t}
  rewrite ggTrans-substitute0 {φ = φ}{t}
  rewrite ggTrans-substitute0 {φ = ψ}{t}
  = [≡]-intro
ggTrans-substitute0 {φ = φ ⟶ ψ}{t}
  rewrite ggTrans-substitute0 {φ = φ}{t}
  rewrite ggTrans-substitute0 {φ = ψ}{t}
  = [≡]-intro
ggTrans-substitute0 {φ = Ɐ φ}{t} = {!!}
  -- rewrite ggTrans-substitute0 {φ = φ}{termVar𝐒 t}
  -- = [≡]-intro
ggTrans-substitute0 {φ = ∃ φ}{t} = {!!}
  -- rewrite ggTrans-substitute0 {φ = φ}{termVar𝐒 t}
  -- = [≡]-intro

koTrans-substitute0 : ∀{t} → (koTrans(substitute0 t φ) ≡ substitute0 t (koTrans φ))
koTrans-substitute0 {φ = f $ x} = [≡]-intro
koTrans-substitute0 {φ = ⊤}     = [≡]-intro
koTrans-substitute0 {φ = ⊥}     = [≡]-intro
koTrans-substitute0 {φ = φ ∧ ψ}{t}
  rewrite koTrans-substitute0 {φ = φ}{t}
  rewrite koTrans-substitute0 {φ = ψ}{t}
  = [≡]-intro
koTrans-substitute0 {φ = φ ∨ ψ}{t}
  rewrite koTrans-substitute0 {φ = φ}{t}
  rewrite koTrans-substitute0 {φ = ψ}{t}
  = [≡]-intro
koTrans-substitute0 {φ = φ ⟶ ψ}{t}
  rewrite koTrans-substitute0 {φ = φ}{t}
  rewrite koTrans-substitute0 {φ = ψ}{t}
  = [≡]-intro
koTrans-substitute0 {φ = Ɐ φ}{t} = {!!}
  -- rewrite koTrans-substitute0 {φ = φ}{termVar𝐒 t}
  -- = [≡]-intro
koTrans-substitute0 {φ = ∃ φ}{t} = {!!}
  -- rewrite koTrans-substitute0 {φ = φ}{termVar𝐒 t}
  -- = [≡]-intro

-- 2.3.4 (ii)
ggTrans-correctnessₗ : (Γ Classical.⊢ φ) ← (map ggTrans Γ ⊢ (ggTrans φ))
ggTrans-correctnessᵣ : (Γ Classical.⊢ φ) → (map ggTrans Γ ⊢ (ggTrans φ))

ggTrans-correctnessᵣ (Classical.direct p) = direct (Meta.[∃]-intro _ ⦃ Meta.[∧]-intro p [≡]-intro ⦄)
ggTrans-correctnessᵣ (Classical.[⊤]-intro) = [⊤]-intro
ggTrans-correctnessᵣ {Γ = Γ}{φ = φ} (Classical.[⊥]-elim p) = [⟶]-elim ([⟶]-intro(weaken{Γ₂ = (map ggTrans Γ) ∪ ·(ggTrans(¬ φ))} map-preserves-union-singleton (ggTrans-correctnessᵣ p))) ([¬¬]-elim-on-negativeFragment ggTrans-negativeFragment)
ggTrans-correctnessᵣ (Classical.[∧]-intro p q) = [∧]-intro (ggTrans-correctnessᵣ p) (ggTrans-correctnessᵣ q)
ggTrans-correctnessᵣ (Classical.[∧]-elimₗ p) = [∧]-elimₗ (ggTrans-correctnessᵣ p)
ggTrans-correctnessᵣ (Classical.[∧]-elimᵣ p) = [∧]-elimᵣ (ggTrans-correctnessᵣ p)
ggTrans-correctnessᵣ (Classical.[∨]-introₗ p) = [⟶]-elim (ggTrans-correctnessᵣ p) [∨]-introₗ-by-[¬¬∧¬]
ggTrans-correctnessᵣ (Classical.[∨]-introᵣ p) = [⟶]-elim (ggTrans-correctnessᵣ p) [∨]-introᵣ-by-[¬¬∧¬]
ggTrans-correctnessᵣ (Classical.[∨]-elim p q r) = [⟶]-elim₃ ([⟶]-intro(weaken map-preserves-union-singleton (ggTrans-correctnessᵣ p))) ([⟶]-intro(weaken map-preserves-union-singleton (ggTrans-correctnessᵣ q))) (ggTrans-correctnessᵣ r) ([∨]-elim-by-[¬¬∧¬] ([¬¬]-elim-on-negativeFragment ggTrans-negativeFragment))
ggTrans-correctnessᵣ (Classical.[⟶]-intro p) = [⟶]-intro (weaken map-preserves-union-singleton (ggTrans-correctnessᵣ p))
ggTrans-correctnessᵣ (Classical.[⟶]-elim p q) = [⟶]-elim (ggTrans-correctnessᵣ p) (ggTrans-correctnessᵣ q)
ggTrans-correctnessᵣ (Classical.[Ɐ]-intro p) = [Ɐ]-intro (substitute₁ᵣ(_ ⊢_) ggTrans-substitute0 (ggTrans-correctnessᵣ p))
ggTrans-correctnessᵣ (Classical.[Ɐ]-elim p) = substitute₁ₗ(_ ⊢_) ggTrans-substitute0 ([Ɐ]-elim (ggTrans-correctnessᵣ p))
ggTrans-correctnessᵣ (Classical.[∃]-intro p) = [⟶]-elim (substitute₁ᵣ(_ ⊢_) ggTrans-substitute0 (ggTrans-correctnessᵣ p)) [∃]-intro-by-[¬Ɐ¬]
ggTrans-correctnessᵣ (Classical.[∃]-elim p q) = [⟶]-elim ([⟶]-intro ([⟶]-elim ([Ɐ]-intro ([⟶]-intro ([⟶]-elim (weaken {!map-preserves-union-singleton!} (ggTrans-correctnessᵣ p)) (direct (Left (Right [≡]-intro)))))) (weaken-union (ggTrans-correctnessᵣ q)))) ([¬¬]-elim-on-negativeFragment ggTrans-negativeFragment)

koTrans-stability : Stable{ℓ}(koTrans(φ))
koTrans-stability {φ = f $ x} = [¬¬¬]-elim
koTrans-stability {φ = ⊤}     = [⟶]-intro [⊤]-intro
koTrans-stability {φ = ⊥}     = [⟶]-intro ([⟶]-elim [⟶]-refl (direct (Right [≡]-intro)))
koTrans-stability {φ = φ ∧ ψ} = [¬¬¬]-elim
koTrans-stability {φ = φ ∨ ψ} = [¬¬¬]-elim
koTrans-stability {φ = φ ⟶ ψ} = [¬¬¬]-elim
koTrans-stability {φ = Ɐ φ}   = [¬¬¬]-elim
koTrans-stability {φ = ∃ φ}   = [¬¬¬]-elim

{-
koTrans-to-[¬¬] : Γ ⊢ (koTrans(φ) ⟶ (¬¬ φ))
koTrans-to-[¬¬] {φ = f $ x} = [⟶]-refl
koTrans-to-[¬¬] {φ = ⊤}     = [¬¬]-intro-[⟶]
koTrans-to-[¬¬] {φ = ⊥}     = [¬¬]-intro-[⟶]
koTrans-to-[¬¬] {φ = φ ∧ ψ} = [⟶]-intro ([⟷]-elimₗ ([⟶]-elim₃ koTrans-to-[¬¬] koTrans-to-[¬¬] {!!} [∧]-map) [¬¬]-preserve-[∧])
koTrans-to-[¬¬] {φ = φ ∨ ψ} = {!!}
koTrans-to-[¬¬] {φ = φ ⟶ ψ} = {!!}
koTrans-to-[¬¬] {φ = Ɐ φ}   = {!!}
koTrans-to-[¬¬] {φ = ∃ φ}   = {!!}
-}

ggTrans-koTransₗ : Γ ⊢ ((ggTrans φ) ⟵ (koTrans φ))
ggTrans-koTransᵣ : Γ ⊢ ((ggTrans φ) ⟶ (koTrans φ))

[∧]-elimₗ-koTrans : (Γ ⊢ (koTrans(φ ∧ ψ) ⟶ koTrans(φ)))
[∧]-elimₗ-koTrans = [⟶]-intro ([∧]-elimₗ ([⟶]-elim₃ koTrans-stability koTrans-stability ([⟷]-elimᵣ (direct (Right [≡]-intro)) [¬¬]-preserve-[∧]) [∧]-map))

[∧]-elimᵣ-koTrans : (Γ ⊢ (koTrans(φ ∧ ψ) ⟶ koTrans(ψ)))
[∧]-elimᵣ-koTrans = [⟶]-intro ([∧]-elimᵣ ([⟶]-elim₃ koTrans-stability koTrans-stability ([⟷]-elimᵣ (direct (Right [≡]-intro)) [¬¬]-preserve-[∧]) [∧]-map))

-- [⟶]-elim-koTrans : (Γ ⊢ (koTrans(φ) ⟶ koTrans(φ ⟶ ψ) ⟶ koTrans(ψ)))

-- [⟶]-intro ([⟶]-elim ([∧]-elimₗ ([⟷]-elimᵣ ([⟶]-intro-inverse {![¬¬]-intro-[⟶]!}) [¬¬]-preserve-[∧])) koTrans-stability)
-- {![∧]-elimₗ(Meta.[↔]-to-[→] [¬¬][∧] Γφψ)!}

-- [¬]-preserve-[∨][∧] : Γ ⊢ (¬(φ ∨ ψ) ⟷ ((¬ φ) ∧ (¬ ψ)))

-- Alternative proof of the (_∧_)-case:
--   [⟶]-intro ([∧]-intro
--     ([⟶]-elim ([⟶]-elim (direct (Right [≡]-intro)) [∧]-elimₗ-koTrans) (weaken-union(ggTrans-koTransₗ {φ = φ})))
--     ([⟶]-elim ([⟶]-elim (direct (Right [≡]-intro)) [∧]-elimᵣ-koTrans) (weaken-union(ggTrans-koTransₗ {φ = ψ})))
--   )
ggTrans-koTransₗ {φ = P $ x} = [⟶]-refl
ggTrans-koTransₗ {φ = ⊤}     = [⟶]-refl
ggTrans-koTransₗ {φ = ⊥}     = [⟶]-refl
ggTrans-koTransₗ {φ = φ ∧ ψ} = [⟶]-elim₃
  ([⟶]-elim₂ ([⟷]-to-[⟶] [¬¬]-preserve-[∧]) ([⟶]-elim₂ koTrans-stability koTrans-stability [∧]-map) [⟶]-trans)
  [⟶]-refl
  ([⟶]-elim₂ (ggTrans-koTransₗ {φ = φ}) (ggTrans-koTransₗ {φ = ψ}) [∧]-map)
  [⟶]-map
ggTrans-koTransₗ {φ = φ ∨ ψ} = [⟶]-elim₃
  ([⟶]-elim ([⟷]-to-[⟵] [¬]-preserve-[∨][∧]) [⟶]-contrapositiveᵣ)
  [⟶]-refl
  ([⟶]-elim ([⟶]-elim₂ ([⟶]-elim (ggTrans-koTransₗ {φ = φ}) [¬]-map) ([⟶]-elim (ggTrans-koTransₗ {φ = ψ}) [¬]-map) [∧]-map) [¬]-map)
  [⟶]-map
ggTrans-koTransₗ {φ = φ ⟶ ψ} = [⟶]-elim₃
  (([⟶]-elim₂ [¬¬]-preserve-[⟶] ([⟶]-elim₂ [¬¬]-intro-[⟶] koTrans-stability [⟶]-map) [⟶]-trans))
  [⟶]-refl
  (([⟶]-elim₂ (ggTrans-koTransᵣ {φ = φ}) (ggTrans-koTransₗ {φ = ψ}) [⟶]-map))
  [⟶]-map
ggTrans-koTransₗ {Γ = Γ}{φ = Ɐ φ} = [⟶]-elim₃
  ([⟶]-elim₂ [¬¬]-preserve-[Ɐ] ([⟶]-elim ([Ɐ]-intro (substitute₁ᵣ(\φ → Γ ⊢ ((¬¬ φ) ⟶ φ)) koTrans-substitute0 koTrans-stability)) ([Ɐ]-map {φ₂ = koTrans φ})) [⟶]-trans)
  [⟶]-refl
  ([⟶]-elim ([Ɐ]-intro (substitute₂ᵣ(\a b → Γ ⊢ (a ⟵ b)) ggTrans-substitute0 koTrans-substitute0 (ggTrans-koTransₗ {φ = substitute0 _ φ}))) [Ɐ]-map)
  [⟶]-map
ggTrans-koTransₗ {φ = ∃ φ} = [⟶]-elim₃
  ([⟶]-elim ([⟷]-to-[⟵] [¬]-preserve-[∃][Ɐ]) [⟶]-contrapositiveᵣ)
  [⟶]-refl
  ([⟶]-elim ([⟶]-elim ([Ɐ]-intro ([⟶]-elim (substitute₂ᵣ(\a b → _ ⊢ (a ⟵ b)) ggTrans-substitute0 koTrans-substitute0 (ggTrans-koTransₗ {φ = substitute0 _ φ})) [¬]-map)) [Ɐ]-map) [¬]-map)
  [⟶]-map

ggTrans-koTransᵣ {φ = P $ x} = [⟶]-refl
ggTrans-koTransᵣ {φ = ⊤}     = [⟶]-refl
ggTrans-koTransᵣ {φ = ⊥}     = [⟶]-refl
ggTrans-koTransᵣ {φ = φ ∧ ψ} =
  [⟶]-intro ([¬¬]-intro ([∧]-intro
    ([⟶]-elim ([∧]-elimₗ (direct (Right [≡]-intro))) (weaken-union(ggTrans-koTransᵣ {φ = φ})))
    ([⟶]-elim ([∧]-elimᵣ (direct (Right [≡]-intro))) (weaken-union(ggTrans-koTransᵣ {φ = ψ})))
  ))
ggTrans-koTransᵣ {φ = φ ∨ ψ} =
  [⟶]-intro ([¬¬]-intro ([⟶]-elim₃
    {!!}
    {!!}
    {!direct (Right [≡]-intro)!}
    ([∨]-elim-by-[¬¬∧¬] {!koTrans-stability!})
  ))
ggTrans-koTransᵣ {φ = φ ⟶ ψ} =
  [⟶]-intro ([¬¬]-intro ([⟶]-intro
    ([⟶]-elim
      ([⟶]-elim ([⟵]-elim (direct (Right [≡]-intro)) (weaken-union(weaken-union(ggTrans-koTransₗ {φ = φ})))) (direct (Left (Right [≡]-intro))))
      (weaken-union(weaken-union(ggTrans-koTransᵣ {φ = ψ})))
    )
  ))
ggTrans-koTransᵣ {φ = Ɐ φ}   = {!!}
ggTrans-koTransᵣ {φ = ∃ φ}   = {!!}

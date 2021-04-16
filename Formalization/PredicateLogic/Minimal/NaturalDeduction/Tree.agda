open import Formalization.PredicateLogic.Signature

module Formalization.PredicateLogic.Minimal.NaturalDeduction.Tree (𝔏 : Signature) where
open Signature(𝔏)

open import Data.DependentWidthTree as Tree hiding (height)
import      Lvl
open import Formalization.PredicateLogic.Minimal.NaturalDeduction (𝔏)
open import Formalization.PredicateLogic.Syntax(𝔏)
open import Functional using (_∘_ ; _∘₂_ ; _∘₃_ ; _∘₄_ ; swap ; _←_)
open import Numeral.Finite
open import Numeral.Natural.Relation.Order
open import Numeral.Natural
open import Sets.PredicateSet using (PredSet ; _∈_ ; _∉_ ; _∪_ ; _∪•_ ; _∖_ ; _⊆_ ; _⊇_ ; ∅ ; [≡]-to-[⊆] ; [≡]-to-[⊇] ; map ; unmap) renaming (•_ to · ; _≡_ to _≡ₛ_)
open import Structure.Relator
open import Type.Properties.Inhabited
open import Type

module _ {vars} ⦃ pos-term : ◊(Term(vars)) ⦄ where
  private variable ℓ : Lvl.Level
  private variable Γ Γ₁ Γ₂ : PredSet{ℓ}(Formula(vars))
  private variable φ ψ γ φ₁ ψ₁ γ₁ φ₂ ψ₂ γ₂ φ₃ ψ₃ φ₄ ψ₄ φ₅ ψ₅ δ₁ δ₂ : Formula(vars)

  {-
  height : Term(_) → (Γ ⊢ φ) → ℕ
  height t (direct p)         = 𝟎
  height t [⊤]-intro          = 𝟎
  height t ([∧]-intro  p q)   = 𝐒((height t p) ⦗ max ⦘ᵣ (height t q))
  height t ([∧]-elimₗ  p)     = 𝐒(height t p)
  height t ([∧]-elimᵣ  p)     = 𝐒(height t p)
  height t ([∨]-introₗ p)     = 𝐒(height t p)
  height t ([∨]-introᵣ p)     = 𝐒(height t p)
  height t ([∨]-elim   p q r) = 𝐒((height t p) ⦗ max ⦘ᵣ (height t q) ⦗ max ⦘ᵣ (height t r))
  height t ([⟶]-intro  p)     = 𝐒(height t p)
  height t ([⟶]-elim   p q)   = 𝐒((height t p) ⦗ max ⦘ᵣ (height t q))
  height t ([Ɐ]-intro  p)     = 𝐒(height t (p{t}))
  height t ([Ɐ]-elim   p)     = 𝐒(height t p)
  height t ([∃]-intro  p)     = 𝐒(height t p)
  height t ([∃]-elim   p q)   = 𝐒((height t (p{t})) ⦗ max ⦘ᵣ (height t q))

  test : ∀{t : Term(n)}{p q : Γ ⊢ φ} → (height t p ≤ height t ([∧]-intro p q))
  test = [≤]-successor max-orderₗ
  -}

  tree : (Γ ⊢ φ) → FiniteTreeStructure
  tree(direct x)         = Node 0 \()
  tree [⊤]-intro         = Node 0 \()
  tree([∧]-intro  p q)   = Node 2 \{𝟎 → tree p; (𝐒 𝟎) → tree q}
  tree([∧]-elimₗ  p)     = Node 1 \{𝟎 → tree p}
  tree([∧]-elimᵣ  p)     = Node 1 \{𝟎 → tree p}
  tree([∨]-introₗ p)     = Node 1 \{𝟎 → tree p}
  tree([∨]-introᵣ p)     = Node 1 \{𝟎 → tree p}
  tree([∨]-elim   p q r) = Node 3 \{𝟎 → tree p ; (𝐒 𝟎) → tree q ; (𝐒(𝐒 𝟎)) → tree r}
  tree([⟶]-intro  p)     = Node 1 \{𝟎 → tree p}
  tree([⟶]-elim   p q)   = Node 2 \{𝟎 → tree p ; (𝐒 𝟎) → tree q}
  tree([Ɐ]-intro  p)     = Node 1 \{𝟎 → tree (p{[◊]-existence})}
  tree([Ɐ]-elim   p)     = Node 1 \{𝟎 → tree p}
  tree([∃]-intro  p)     = Node 1 \{𝟎 → tree p}
  tree([∃]-elim   p q)   = Node 2 \{𝟎 → tree (p{[◊]-existence}) ; (𝐒 𝟎) → tree q}

  height : (Γ ⊢ φ) → ℕ
  height = Tree.height ∘ tree

  open import Data.Tuple as Tuple using (_⨯_ ; _,_)
  import      Functional.Dependent
  open        Functional using (_on₂_)
  open import Numeral.Natural.Induction
  open import Numeral.Natural.Inductions  
  open import Numeral.Natural.Relation.Order.Proofs
  open import Structure.Relator.Ordering
  open import Structure.Relator.Ordering.Proofs
  open import Type.Dependent

  -- Ordering of natural deduction proofs on height.
  _<⊢↑_ : Σ(PredSet{ℓ}(Formula(vars)) ⨯ Formula(vars))(Tuple.uncurry(_⊢_)) → Σ(PredSet(Formula(vars)) ⨯ Formula(vars))(Tuple.uncurry(_⊢_)) → Type
  _<⊢↑_ = (_<_) on₂ (height Functional.Dependent.∘ Σ.right)

  instance
    [<⊢↑]-wellfounded : Strict.Properties.WellFounded(_<⊢↑_ {ℓ})
    [<⊢↑]-wellfounded = wellfounded-image-by-trans {f = height Functional.Dependent.∘ Σ.right}

  -- induction-on-height : ∀{P : ∀{Γ : PredSet{ℓₚ}(Formula(vars))}{φ} → (Γ ⊢ φ) → Type{ℓ}} → (∀{x : Prop(vars)} → P(direct x)) → P([⊤]-intro) → (∀{p₂ : Γ ⊢ φ} → (∀{Γ₁}{φ₁}{p₁ : Γ₁ ⊢ φ₁} → (height p₁ < height p₂) → P(p₁)) → P(p₂)) → (∀{p : (Γ ⊢ φ)} → P(p))
  -- induction-on-height {Γ = Γ}{φ = φ} {P = P} dir top step {p} = Strict.Properties.wellfounded-induction(_<⊢↑_) {P = P Functional.Dependent.∘ Σ.right} {!!} {intro (Γ , φ) p}

  -- substitute0-height : ∀{t} → height(substitute0 t φ) ≡ 

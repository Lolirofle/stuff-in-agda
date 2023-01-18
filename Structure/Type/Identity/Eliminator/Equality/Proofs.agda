module Structure.Type.Identity.Eliminator.Equality.Proofs where

open import Function as Fn using (_→ᶠ_)
open import Functional using (_$_ ; _on₂_ ; _∘_)
open import Functional.Instance
import      Lvl
open import Logic
-- open import Structure.Categorical.Properties
open import Structure.Function
open import Structure.Operator
open import Structure.Relator.Equivalence
import      Structure.Relator.Names as Names
open import Structure.Relator
open import Structure.Relator.Properties
open import Structure.Relator.Properties.Proofs
open import Structure.Setoid
open import Structure.Type.Identity
open import Structure.Type.Identity.Eliminator.Equality
import      Structure.Type.Identity.Eliminator.Functions
open import Structure.Type.Identity.MinimalReflexiveRelation.Equality
open import Structure.Type.Identity.Proofs
open import Syntax.Function
open import Syntax.Transitivity
open import Type

private variable ℓ ℓ₁ ℓ₂ ℓₑ₁ ℓₑ₂ ℓₑ₃ ℓₑ ℓₘₑ ℓₚ ℓₚ₁ ℓₚ₂ ℓₒ : Lvl.Level
private variable T A B C : Type{ℓ}
private variable f g : A → B
private variable x y z w : T
private variable Id _▫_ : T → T → Stmt{ℓ}

open IdentityEliminationOfIntro ⦃ … ⦄ renaming (proof to idCompute)

module _
  (Id : A → A → Type{ℓₑ₁}) ⦃ intro :  Reflexivity(Id) ⦄  ⦃ elim : ∀{ℓₚ} → IdentityEliminator(Id) {ℓₚ} ⦄
  {ℓₑ : Lvl.Level → Lvl.Level} (_≡_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Type{ℓₑ(ℓ)})
  ⦃ identElimOfIntro : ∀{ℓₚ}{P : ∀{x y} → Id x y → Type{ℓₚ}} → IdentityEliminationOfIntro(Id) P (_≡_) ⦄
  where

  open Structure.Type.Identity.Eliminator.Functions.Oper(Id) ⦃ intro ⦄ ⦃ elim ⦄

  transₗ-of-refl-is-id : trans{x}{x}{y}(refl{x}) ≡ Fn.id
  transₗ-of-refl-is-id = idCompute Fn.id

  flippedTransᵣ-of-refl-is-id : flippedTransᵣ{x}{x}{y}(refl{x}) ≡ Fn.id
  flippedTransᵣ-of-refl-is-id = idCompute Fn.id

  module _ {_▫_ : A → A → Type{ℓₑ₂}} ⦃ refl-op : Reflexivity(_▫_) ⦄ where
    sub-of-refl : (sub(_▫_) (refl{x}) ≡ reflexivity(_▫_) {x})
    sub-of-refl = idCompute(reflexivity(_▫_))

module _
  (Id : A → A → Type{ℓₑ₁}) ⦃ intro :  Reflexivity(Id) ⦄  ⦃ elim : ∀{ℓₚ} → IdentityEliminator(Id) {ℓₚ} ⦄
  {ℓₑ : Lvl.Level → Lvl.Level} (_≡_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Type{ℓₑ(ℓ)}) ⦃ ident : IdentityType(_≡_) ⦄
  ⦃ identElimOfIntro : ∀{ℓₚ}{P : ∀{x y} → Id x y → Type{ℓₚ}} → IdentityEliminationOfIntro(Id) P (_≡_) ⦄
  where

  open Structure.Type.Identity.Eliminator.Functions.Oper(Id) ⦃ intro ⦄ ⦃ elim ⦄
  private instance _ = \{ℓ}{T} → identityEliminator-to-equiv{ℓ}{T} ⦃ IdentityType.introduction-rule ident ⦄ ⦃ IdentityType.elimination-rule ident ⦄
  private variable e : Id x y

  transₗ-of-refl : trans(refl{x}) e ≡ e
  transₗ-of-refl{e = e} = congruence₁(_$ e) ⦃ identityEliminator-to-function ⦄ (transₗ-of-refl-is-id(Id)(_≡_))

  {-
  instance
    comp-refl-identityₗ : Morphism.Identityᵣ(\{x} → comp{x})(refl)
    comp-refl-identityₗ = Morphism.intro transₗ-of-refl
  -}

module _
  (Id : A → A → Type{ℓₑ₁}) ⦃ intro :  Reflexivity(Id) ⦄ ⦃ elim : ∀{ℓₚ} → IdentityEliminator(Id) {ℓₚ} ⦄
  (_≡_ : ∀{x y} → Id x y → Id x y → Type{ℓₑ₂})
  ⦃ identElimOfIntro : ∀{X Y : ∀{x y} → Id x y → A} → IdentityEliminationOfIntro(Id) (\e → Id (X e) (Y e)) (_≡_) ⦄
  where

  open Structure.Type.Identity.Eliminator.Functions.Oper(Id) ⦃ intro ⦄ ⦃ elim ⦄
  private instance _ = identityEliminator-to-equiv ⦃ intro ⦄ ⦃ elim ⦄

  sym-of-refl : sym(refl{x}) ≡ refl{x}
  sym-of-refl{x} = idCompute refl

module _
  (Id : A → A → Type{ℓₑ₁}) ⦃ intro :  Reflexivity(Id) ⦄  ⦃ elim : ∀{ℓₚ} → IdentityEliminator(Id) {ℓₚ} ⦄
  ⦃ equiv-Id : ∀{x y} → Equiv{ℓₑ₂}(Id x y) ⦄
  ⦃ identElimOfIntro : ∀{X Y : ∀{x y} → Id x y → A} → IdentityEliminationOfIntro(Id) (\e → Id (X e) (Y e)) (_≡_) ⦄
  where

  open Structure.Type.Identity.Eliminator.Functions.Oper(Id) ⦃ intro ⦄ ⦃ elim ⦄
  private instance _ = identityEliminator-to-equiv ⦃ intro ⦄ ⦃ elim ⦄

  private variable e e₁ : Id x y
  private variable e₂ : Id y z
  private variable e₃ : Id z w

  module _ (transₗ-of-refl : ∀{x y}{e : Id x y} → (trans refl e ≡ e)) where
    private module _ {x}{y} where open Equiv(equiv-Id{x}{y}) using () renaming (reflexivity to [≡]-reflexivity ; symmetry to [≡]-symmetry ; transitivity to [≡]-transitivity) public

    trans-of-refl : trans refl refl ≡ refl{x}
    trans-of-refl = transₗ-of-refl

    transᵣ-of-refl : trans e (refl{x}) ≡ e
    transᵣ-of-refl{e = e} = idElim(Id) (e ↦ trans e refl ≡ e) trans-of-refl e

    module _ ⦃ trans-func : ∀{x y z} → BinaryOperator(trans{x}{y}{z}) ⦄ where
      transₗ-of-sym : trans(sym e) e ≡ refl
      transₗ-of-sym{e = e} = idElim(Id) (e ↦ trans(sym e) e ≡ refl)
        (
          trans(sym refl) refl 🝖[ _≡_ ]-[ congruence₂-₁(trans)(refl) (sym-of-refl(Id)(_≡_)) ]
          trans refl refl      🝖[ _≡_ ]-[ trans-of-refl ]
          refl                 🝖-end
        )
        e

      transᵣ-of-sym : trans e (sym e) ≡ refl
      transᵣ-of-sym{e = e} = idElim(Id) (e ↦ trans e (sym e) ≡ refl)
        (
          trans refl (sym refl) 🝖[ _≡_ ]-[ congruence₂-₂(trans)(refl) (sym-of-refl(Id)(_≡_)) ]
          trans refl refl       🝖[ _≡_ ]-[ trans-of-refl ]
          refl                  🝖-end
        )
        e

      trans-assoc : trans(trans e₁ e₂) e₃ ≡ trans e₁ (trans e₂ e₃)
      trans-assoc{e₁ = e₁}{e₂ = e₂}{e₃ = e₃} = idElimFixedₗ(Id) (e₁ ↦ trans(trans e₁ e₂) e₃ ≡ trans e₁ (trans e₂ e₃))
        (
          trans(trans refl e₂) e₃  🝖[ _≡_ ]-[ congruence₂-₁(trans)(e₃) transₗ-of-refl ]
          trans e₂ e₃              🝖[ _≡_ ]-[ transₗ-of-refl ]-sym
          trans refl (trans e₂ e₃) 🝖-end
        )
        e₁

    module _ ⦃ sym-func : ∀{x y} → Function(sym{x}{y}) ⦄ where
      sym-of-sym : sym(sym e) ≡ e
      sym-of-sym{e = e} = idElim(Id) (e ↦ sym(sym e) ≡ e)
        (
          sym(sym refl) 🝖[ _≡_ ]-[ congruence₁(sym) (sym-of-refl(Id)(_≡_)) ]
          sym refl      🝖[ _≡_ ]-[ sym-of-refl(Id)(_≡_) ]
          refl          🝖-end
        )
        e

    module _
      ⦃ sym-func : ∀{x y} → Function(sym{x}{y}) ⦄
      ⦃ trans-func : ∀{x y z} → BinaryOperator(trans{x}{y}{z}) ⦄
      where

      sym-of-trans : sym(trans e₁ e₂) ≡ trans(sym e₂) (sym e₁)
      sym-of-trans{e₁ = e₁}{e₂ = e₂} = idElimFixedᵣ(Id) (e₂ ↦ sym(trans e₁ e₂) ≡ trans(sym e₂) (sym e₁))
        (
          sym(trans e₁ refl)       🝖[ _≡_ ]-[ congruence₁(sym) transᵣ-of-refl ]
          sym e₁                   🝖[ _≡_ ]-[ transₗ-of-refl ]-sym
          trans refl (sym e₁)      🝖[ _≡_ ]-[ congruence₂-₁(trans)(sym e₁) (sym-of-refl(Id)(_≡_)) ]-sym
          trans(sym refl) (sym e₁) 🝖-end
        )
        e₂

module _
  (Id₁ : A → A → Type{ℓₑ₁}) ⦃ intro₁ :  Reflexivity(Id₁) ⦄ ⦃ elim₁ : ∀{ℓₚ} → IdentityEliminator(Id₁) {ℓₚ} ⦄
  (Id₂ : B → B → Type{ℓₑ₂}) ⦃ intro₂ :  Reflexivity(Id₂) ⦄ ⦃ elim₂ : ∀{ℓₚ} → IdentityEliminator(Id₂) {ℓₚ} ⦄
  {ℓₑ : Lvl.Level → Lvl.Level} (_≡_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Type{ℓₑ(ℓ)})
  ⦃ identElimOfIntro₁ : ∀{ℓₚ}{P : ∀{x y} → Id₁ x y → Type{ℓₚ}} → IdentityEliminationOfIntro(Id₁) P (_≡_) ⦄
  where

  open Structure.Type.Identity.Eliminator.Functions.Oper hiding (cong)
  open Structure.Type.Identity.Eliminator.Functions.Oper₂ using (cong)

  cong-of-refl : cong(Id₁)(Id₂) f (refl(Id₁) {x}) ≡ refl(Id₂) {f(x)}
  cong-of-refl{f = f} = idCompute{Id = Id₁} (reflexivity(Id₂ on₂ f) ⦃ on₂-reflexivity ⦄)

module _
  (Id₁ : A → A → Type{ℓₑ₁}) ⦃ intro₁ :  Reflexivity(Id₁) ⦄  ⦃ elim₁ : ∀{ℓₚ} → IdentityEliminator(Id₁) {ℓₚ} ⦄
  (Id₂ : B → B → Type{ℓₑ₂}) ⦃ intro₂ :  Reflexivity(Id₂) ⦄  ⦃ elim₂ : ∀{ℓₚ} → IdentityEliminator(Id₂) {ℓₚ} ⦄
  {ℓₑ : Lvl.Level → Lvl.Level} (_≡_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Type{ℓₑ(ℓ)}) ⦃ [≡]-equivalence : ∀{ℓ}{T} → Equivalence(_≡_ {ℓ}{T}) ⦄
  ⦃ identElimOfIntro₁ : ∀{ℓₚ}{P : ∀{x y} → Id₁ x y → Type{ℓₚ}} → IdentityEliminationOfIntro(Id₁) P (_≡_) ⦄
  ⦃ identElimOfIntro₂ : ∀{ℓₚ}{P : ∀{x y} → Id₂ x y → Type{ℓₚ}} → IdentityEliminationOfIntro(Id₂) P (_≡_) ⦄
  where

  open Structure.Type.Identity.Eliminator.Functions.Oper hiding (cong)
  open Structure.Type.Identity.Eliminator.Functions.Oper₂ using (cong)
  private module _ {ℓ}{T} where open Equivalence([≡]-equivalence {ℓ}{T}) renaming (reflexivity to [≡]-reflexivity ; symmetry to [≡]-symmetry ; transitivity to [≡]-transitivity) public
  private instance _ = \{ℓ}{T} → Structure.Setoid.intro(_≡_)  ⦃ [≡]-equivalence {ℓ}{T} ⦄
  private variable e e₁ : Id₁ x y
  private variable e₂ : Id₁ y z

  module _
    ⦃ sym₂-func : ∀{x y} → Function(sym(Id₂) {x}{y}) ⦄
    ⦃ congᵣ-func : ∀{x y}{f} → Function(cong(Id₁)(Id₂) f{x}{y}) ⦄
    where

    cong-of-sym : cong(Id₁)(Id₂) f(sym(Id₁) {x}{y} e) ≡ sym(Id₂) (cong(Id₁)(Id₂) f e)
    cong-of-sym{f = f}{e = e} = idElim(Id₁) (e ↦ cong(Id₁)(Id₂) f(sym(Id₁) e) ≡ sym(Id₂) (cong(Id₁)(Id₂) f e))
      (
        cong(Id₁)(Id₂) f(sym(Id₁) (refl(Id₁))) 🝖[ _≡_ ]-[ congruence₁(cong(Id₁)(Id₂) f) (sym-of-refl(Id₁)(_≡_)) ]
        cong(Id₁)(Id₂) f(refl(Id₁))            🝖[ _≡_ ]-[ cong-of-refl(Id₁)(Id₂)(_≡_) ]
        refl(Id₂)                              🝖[ _≡_ ]-[ sym-of-refl(Id₂)(_≡_) ]-sym
        sym(Id₂) (refl(Id₂))                   🝖[ _≡_ ]-[ congruence₁(sym(Id₂)) (cong-of-refl(Id₁)(Id₂)(_≡_)) ]-sym
        sym(Id₂) (cong(Id₁)(Id₂) f(refl(Id₁))) 🝖-end
      )
      e

  module _
    ⦃ trans-func : ∀{x y z} → BinaryOperator(trans(Id₂) {x}{y}{z}) ⦄
    ⦃ congᵣ-func : ∀{x y}{f} → Function(cong(Id₁)(Id₂) f{x}{y}) ⦄
    (transₗ-of-refl₁ : ∀{x y}{e : Id₁ x y} → (trans(Id₁) (refl(Id₁)) e ≡ e))
    (transₗ-of-refl₂ : ∀{x y}{e : Id₂ x y} → (trans(Id₂) (refl(Id₂)) e ≡ e))
    where

    cong-of-trans : cong(Id₁)(Id₂) f(trans(Id₁) {x}{y}{z} e₁ e₂) ≡ trans(Id₂) (cong(Id₁)(Id₂) f e₁) (cong(Id₁)(Id₂) f e₂)
    cong-of-trans{f = f}{e₁ = e₁}{e₂ = e₂} = idElimFixedₗ(Id₁) (e₁ ↦ cong(Id₁)(Id₂) f(trans(Id₁) e₁ e₂) ≡ trans(Id₂) (cong(Id₁)(Id₂) f e₁) (cong(Id₁)(Id₂) f e₂))
      (
        cong(Id₁)(Id₂) f(trans(Id₁) (refl(Id₁)) e₂)                     🝖[ _≡_ ]-[ congruence₁(cong(Id₁)(Id₂) f) transₗ-of-refl₁ ]
        cong(Id₁)(Id₂) f(e₂)                                            🝖[ _≡_ ]-[ transₗ-of-refl₂ ]-sym
        trans(Id₂) (refl(Id₂)) (cong(Id₁)(Id₂) f(e₂))                   🝖[ _≡_ ]-[ congruence₂-₁(trans(Id₂))(cong(Id₁)(Id₂) f(e₂)) (cong-of-refl(Id₁)(Id₂)(_≡_)) ]-sym
        trans(Id₂) (cong(Id₁)(Id₂) f(refl(Id₁))) (cong(Id₁)(Id₂) f(e₂)) 🝖-end
      )
      e₁

module _
  (Id : A → A → Type{ℓₑ}) ⦃ intro :  Reflexivity(Id) ⦄ ⦃ elim : ∀{ℓₚ} → IdentityEliminator(Id) {ℓₚ} ⦄
  {ℓₑ : Lvl.Level → Lvl.Level} (_≡_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Type{ℓₑ(ℓ)})
  ⦃ identElimOfIntro : ∀{ℓₚ}{P : ∀{x y} → Id x y → Type{ℓₚ}} → IdentityEliminationOfIntro(Id) P (_≡_) ⦄
  where

  open Structure.Type.Identity.Eliminator.Functions.Oper(Id) ⦃ intro ⦄ ⦃ elim ⦄
  private variable e : Id x y

  cong-of-id : cong Fn.id(e) ≡ e
  cong-of-id {e = e} = idElim(Id) (e ↦ cong Fn.id(e) ≡ e) (cong-of-refl(Id)(Id)(_≡_)) e


module _
  (Id₁ : A → A → Type{ℓₑ₁}) ⦃ intro₁ :  Reflexivity(Id₁) ⦄ ⦃ elim₁ : ∀{ℓₚ} → IdentityEliminator(Id₁) {ℓₚ} ⦄
  (Id₂ : B → B → Type{ℓₑ₂}) ⦃ intro₂ :  Reflexivity(Id₂) ⦄ ⦃ elim₂ : ∀{ℓₚ} → IdentityEliminator(Id₂) {ℓₚ} ⦄
  (Id₃ : C → C → Type{ℓₑ₃}) ⦃ intro₃ :  Reflexivity(Id₃) ⦄ ⦃ elim₃ : ∀{ℓₚ} → IdentityEliminator(Id₃) {ℓₚ} ⦄
  {ℓₑ : Lvl.Level → Lvl.Level} (_≡_ : ∀{ℓ}{T : Type{ℓ}} → T → T → Type{ℓₑ(ℓ)}) ⦃ [≡]-equivalence : ∀{ℓ}{T} → Equivalence(_≡_ {ℓ}{T}) ⦄
  ⦃ identElimOfIntro₁ : ∀{ℓₚ}{P : ∀{x y} → Id₁ x y → Type{ℓₚ}} → IdentityEliminationOfIntro(Id₁) P (_≡_) ⦄
  ⦃ identElimOfIntro₂ : ∀{ℓₚ}{P : ∀{x y} → Id₂ x y → Type{ℓₚ}} → IdentityEliminationOfIntro(Id₂) P (_≡_) ⦄
  where

  open Structure.Type.Identity.Eliminator.Functions.Oper hiding (cong)
  open Structure.Type.Identity.Eliminator.Functions.Oper₂ using (cong)
  private module _ {ℓ}{T} where open Equivalence([≡]-equivalence {ℓ}{T}) renaming (reflexivity to [≡]-reflexivity ; symmetry to [≡]-symmetry ; transitivity to [≡]-transitivity) public
  private instance _ = \{ℓ}{T} → Structure.Setoid.intro(_≡_)  ⦃ [≡]-equivalence {ℓ}{T} ⦄
  private variable e : Id₁ x y

  module _ ⦃ congᵣ-func : ∀{x y}{f} → Function(cong(Id₂)(Id₃) f{x}{y}) ⦄ where
    cong-of-[∘] : cong(Id₁)(Id₃) (f ∘ g)(e) ≡ cong(Id₂)(Id₃) f(cong(Id₁)(Id₂) g e)
    cong-of-[∘] {f = f}{g = g}{e = e} = idElim(Id₁) (e ↦ cong(Id₁)(Id₃) (f ∘ g)(e) ≡ cong(Id₂)(Id₃) f(cong(Id₁)(Id₂) g e))
      (
        cong(Id₁)(Id₃) (f ∘ g)(refl(Id₁))              🝖[ _≡_ ]-[ cong-of-refl(Id₁)(Id₃)(_≡_) ]
        refl(Id₃)                                      🝖[ _≡_ ]-[ cong-of-refl(Id₂)(Id₃)(_≡_) ]-sym
        cong(Id₂)(Id₃) f(refl(Id₂))                    🝖[ _≡_ ]-[ congruence₁(cong(Id₂)(Id₃) f) (cong-of-refl(Id₁)(Id₂)(_≡_)) ]-sym
        cong(Id₂)(Id₃) f(cong(Id₁)(Id₂) g (refl(Id₁))) 🝖-end
      )
      e

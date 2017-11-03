module Logic.Predicate.Theorems {ℓ₁} {ℓ₂} where

import      Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Propositional.Theorems{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Type

[∀][∃¬]-contradiction : ∀{X}{P : X → Stmt} → (∀{x} → P(x)) → (∃(x ↦ ¬(P(x)))) → ⊥
[∀][∃¬]-contradiction{X}{P} (ap)(enp) =
  ([∃]-elim(\{a} → np ↦ (
    ([⊥]-intro
      ([∀]-elim{X}{P}(ap) {a})
      np
    )
  )) (enp))

[∀]-to-[¬∃¬] : ∀{X}{P : X → Stmt} → (∀{x} → P(x)) → (¬ ∃(x ↦ ¬(P(x))))
[∀]-to-[¬∃¬] = [∀][∃¬]-contradiction -- [∃]-elim(\{a} → npa ↦ npa(p{a}))(ep)

[∃¬]-to-[¬∀] : ∀{X}{P : X → Stmt} → (∃(x ↦ ¬(P(x)))) → (¬ ∀{x} → P(x))
[∃¬]-to-[¬∀] = swap [∀][∃¬]-contradiction

[∀¬¬][∃¬]-contradiction : ∀{X}{P : X → Stmt} → (∀{x} → ¬¬(P(x))) → (∃(x ↦ ¬(P(x)))) → ⊥
[∀¬¬][∃¬]-contradiction{X}{P} (annp)([∃]-intro(a)(na)) =
  [∀][∃¬]-contradiction{X}{¬¬_ ∘ P} (annp)([∃]-intro(a)([¬¬]-intro(na)))

[∀¬¬]-to-[¬∃¬] : ∀{X}{P : X → Stmt} → (∀{x} → ¬¬(P(x))) → (¬ ∃(x ↦ ¬(P(x))))
[∀¬¬]-to-[¬∃¬] = [∀¬¬][∃¬]-contradiction

[¬¬∀]-to-[¬∃¬] : ∀{X}{P : X → Stmt} → ¬¬(∀{x} → (P(x))) → (¬ ∃(x ↦ ¬(P(x))))
[¬¬∀]-to-[¬∃¬] (annx) (enx) =
  ([⊥]-intro
    ([∃¬]-to-[¬∀](enx))
    (annx)
  )

[¬∃¬]-to-[∀¬¬] : ∀{X}{P : X → Stmt} → ¬(∃(x ↦ ¬(P(x)))) → (∀{x} → ¬¬(P(x)))
[¬∃¬]-to-[∀¬¬] {X}{P} (nenx) {a} (npa) = nenx([∃]-intro(a)(npa))

[¬¬∀]-to-[∀¬¬] : ∀{X}{P : X → Stmt} → ¬¬(∀{x} → (P(x))) → (∀{x} → ¬¬(P(x)))
[¬¬∀]-to-[∀¬¬] = [¬∃¬]-to-[∀¬¬] ∘ [¬¬∀]-to-[¬∃¬]

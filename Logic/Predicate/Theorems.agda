module Logic.Predicate.Theorems {ℓ₁} {ℓ₂} where

import      Lvl
open import Data
open import Functional
open import Logic.Propositional{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Propositional.Theorems{ℓ₁ Lvl.⊔ ℓ₂}
open import Logic.Predicate{ℓ₁}{ℓ₂}
open import Type

[∀]-swap : ∀{X Y}{P : X → Y → Stmt} → ∀ₗ(x ↦ ∀ₗ(y ↦ P(x)(y))) → ∀ₗ(y ↦ ∀ₗ(x ↦ P(x)(y)))
[∀]-swap(xypxy){y}{x} = xypxy{x}{y}

[∃]-swap : ∀{X Y}{P : X → Y → Stmt} → ∃(x ↦ ∃(y ↦ P(x)(y))) → ∃(y ↦ ∃(x ↦ P(x)(y)))
[∃]-swap([∃]-intro(x)([∃]-intro(y)(proof))) = [∃]-intro(y)([∃]-intro(x)(proof))

[∃]-irrelevant : ∀{X}{P : Stmt} → ∃{X}(x ↦ P) → P
[∃]-irrelevant([∃]-intro(_)(proof)) = proof

-- TODO: Probably unprovable? X is not guaranteed to not be the empty type, and even if it was, the ∀ function requires a constructed value. Does this require the function/exentional equality axiom?
-- [∀]-irrelevant : ∀{X}{P : Stmt} → ∀ₗ{X}(x ↦ P) → P

[∀]-irrelevant : ∀{X}{P : Stmt} → ∃{X}(x ↦ ⊤) → ∀ₗ{X}(x ↦ P) → P
[∀]-irrelevant([∃]-intro(x)(_)) (f) = f{x}

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
[¬¬∀]-to-[¬∃¬] = contrapositiveᵣ [∃¬]-to-[¬∀]
-- [¬¬∀]-to-[¬∃¬] (annx) (enx) =
--   ([⊥]-intro
--     ([∃¬]-to-[¬∀](enx))
--     (annx)
--   )

[¬∃¬]-to-[∀¬¬] : ∀{X}{P : X → Stmt} → ¬(∃(x ↦ ¬(P(x)))) → (∀{x} → ¬¬(P(x)))
[¬∃¬]-to-[∀¬¬] {X}{P} (nenx) {a} (npa) = nenx([∃]-intro(a)(npa))

[¬¬∀]-to-[∀¬¬] : ∀{X}{P : X → Stmt} → ¬¬(∀{x} → (P(x))) → (∀{x} → ¬¬(P(x)))
[¬¬∀]-to-[∀¬¬] = [¬∃¬]-to-[∀¬¬] ∘ [¬¬∀]-to-[¬∃¬]

-- TODO: Probably unprovable
-- [∀¬¬]-to-[¬¬∀] : ∀{X}{P : X → Stmt} → ¬¬(∀{x} → (P(x))) ← (∀{x} → ¬¬(P(x)))

[∀¬]-to-[¬∃] : ∀{X}{P : X → Stmt} → (∀{x} → ¬(P(x))) → ¬(∃(x ↦ P(x)))
[∀¬]-to-[¬∃] (anpx) =
  ([¬]-intro(epx ↦
    [∃]-elim(\{a} → pa ↦
      ([⊥]-intro
        pa
        (anpx{a})
      )
    )(epx)
  ))

[¬∃]-to-[∀¬] : ∀{X}{P : X → Stmt} → (∀{x} → ¬(P(x))) ← ¬(∃(x ↦ P(x)))
[¬∃]-to-[∀¬] {X}{P} (nepx) =
  ([∀]-intro(a ↦
    (([¬]-intro(pa ↦
      (([⊥]-intro
        (([∃]-intro a pa) :of: (∃(x ↦ P(x))))
        (nepx :of: ¬(∃(x ↦ P(x))))
      ) :of: ⊥)
    )) :of: ¬(P(a)))
  ))

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

-- TODO: Probably unprovable? X is not guaranteed to not be the empty type, and even if it was, the ∀ function requires a constructed value. It seems to need a non-empty domain to quantify over
-- [∀]-irrelevant : ∀{X}{P : Stmt} → ∀ₗ{X}(x ↦ P) → P

[∀][∃¬]-contradiction : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ P(x)) → ∃(x ↦ ¬(P(x))) → ⊥
[∀][∃¬]-contradiction{X}{P} (ap)(enp) =
  ([∃]-elim(\{a} → np ↦ (
    ([⊥]-intro
      ([∀]-elim{X}{P} ap(a))
      np
    )
  )) (enp))

[∀]-to-[¬∃¬] : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ P(x)) → (¬ ∃(x ↦ ¬(P(x))))
[∀]-to-[¬∃¬] = [∀][∃¬]-contradiction -- [∃]-elim(\{a} → npa ↦ npa(p{a}))(ep)

[∃¬]-to-[¬∀] : ∀{X}{P : X → Stmt} → (∃(x ↦ ¬(P(x)))) → (¬ ∀{x} → P(x))
[∃¬]-to-[¬∀] = swap [∀][∃¬]-contradiction

{- TODO: Not sure?
[¬∀]-to-[∃¬] : ∀{X}{P : X → Stmt} → (∃(x ↦ ¬(P(x)))) ← (¬ ∀{x} → P(x))
[¬∀]-to-[∃¬] {X} (napx) = test where
  postulate a : X

  test =
    ([∃]-intro(a)
      ([¬]-intro
        ([⊥]-intro(pa ↦
          ([∀]-intro(pa))
          (napx)
        ))
      )
    )
-}

[∀¬¬][∃¬]-contradiction : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ ¬¬(P(x))) → (∃(x ↦ ¬(P(x)))) → ⊥
[∀¬¬][∃¬]-contradiction{X}{P} (annp)([∃]-intro(a)(na)) =
  [∀][∃¬]-contradiction{X}{¬¬_ ∘ P} (annp)([∃]-intro(a)([¬¬]-intro(na)))

[∀¬¬]-to-[¬∃¬] : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ ¬¬(P(x))) → (¬ ∃(x ↦ ¬(P(x))))
[∀¬¬]-to-[¬∃¬] = [∀¬¬][∃¬]-contradiction

[¬¬∀]-to-[¬∃¬] : ∀{X}{P : X → Stmt} → ¬¬ ∀ₗ(x ↦ (P(x))) → (¬ ∃(x ↦ ¬(P(x))))
[¬¬∀]-to-[¬∃¬] = contrapositiveᵣ [∃¬]-to-[¬∀]
-- [¬¬∀]-to-[¬∃¬] (annx) (enx) =
--   ([⊥]-intro
--     ([∃¬]-to-[¬∀](enx))
--     (annx)
--   )

[¬∃¬]-to-[∀¬¬] : ∀{X}{P : X → Stmt} → ¬(∃(x ↦ ¬(P(x)))) → ∀ₗ(x ↦ ¬¬(P(x)))
[¬∃¬]-to-[∀¬¬] {X}{P} (nenx) {a} (npa) = nenx([∃]-intro(a)(npa))

[¬¬∀]-to-[∀¬¬] : ∀{X}{P : X → Stmt} → ¬¬ ∀ₗ(x ↦ (P(x))) → ∀ₗ(x ↦ ¬¬(P(x)))
[¬¬∀]-to-[∀¬¬] = [¬∃¬]-to-[∀¬¬] ∘ [¬¬∀]-to-[¬∃¬]

-- TODO: Probably unprovable because people said so. Not sure why. Maybe because (¬¬A is valid in constructive logic) ⇔ (A is valid in classical logic), and therefore this would not be possible because everything here is in constructive logic.
-- [∀¬¬]-to-[¬¬∀] : ∀{X}{P : X → Stmt} → ¬¬∀ₗ(x ↦ (P(x))) ← ∀ₗ(x ↦ ¬¬(P(x)))

[∀¬]-to-[¬∃] : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ ¬(P(x))) → ¬(∃(x ↦ P(x)))
[∀¬]-to-[¬∃] (anpx) =
  ([¬]-intro(epx ↦
    [∃]-elim(\{a} → pa ↦
      ([⊥]-intro
        pa
        (anpx{a})
      )
    )(epx)
  ))

[¬∃]-to-[∀¬] : ∀{X}{P : X → Stmt} → ∀ₗ(x ↦ ¬(P(x))) ← ¬(∃(x ↦ P(x)))
[¬∃]-to-[∀¬] {X}{P} (nepx) =
  ([∀]-intro(a ↦
    (([¬]-intro(pa ↦
      (([⊥]-intro
        (([∃]-intro a pa) :of: (∃(x ↦ P(x))))
        (nepx :of: ¬(∃(x ↦ P(x))))
      ) :of: ⊥)
    )) :of: ¬(P(a)))
  ))

-- TODO: Probably unprovable because [∀]-elim seems to need a constructed element?
-- [∀]-to-[∃] : ∀{X}{P : X → Stmt} → ∀(x ↦ P(x)) → ∃(x ↦ P(x))

[∀ₑ]-to-[∃] : ∀{X}{P : X → Stmt} → ∀ₑ(x ↦ P(x)) → ∃(x ↦ P(x))
[∀ₑ]-to-[∃] (apx) =
  [∃]-intro(_)([∀ₑ]-elimₑ(apx))

[∀ₑ]-irrelevant : ∀{X}{P : Stmt} → ∀ₑ{X}(x ↦ P) → P
[∀ₑ]-irrelevant = [∀ₑ]-elimₑ

[∀][→]-elim : ∀{X}{P Q : X → Stmt} → ∀ₗ(x ↦ (P(x) → Q(x))) → ∀ₗ(x ↦ P(x)) → ∀ₗ(x ↦ Q(x))
[∀][→]-elim (PxQx) (Px) = PxQx(Px)

[∀][∧]-combine : ∀{X}{P Q : X → Stmt} → (∀ₗ(x ↦ P(x)) ∧ ∀ₗ(x ↦ Q(x))) → ∀ₗ(x ↦ (P(x) ∧ Q(x)))
[∀][∧]-combine ([∧]-intro (axPx) (axQx)) {x} = [∧]-intro (axPx{x}) (axQx{x})

[∀][→]ᵣ-unmentionedᵣ : ∀{X}{P : Stmt}{Q : X → Stmt} → ∀ₗ(x ↦ (P → Q(x))) → (P → ∀ₗ(x ↦ Q(x)))
[∀][→]ᵣ-unmentionedᵣ (xPQx) (P) {x} = xPQx(P)

[∀][→]ᵣ-unmentionedₗ : ∀{X}{P : Stmt}{Q : X → Stmt} → ∀ₗ(x ↦ (P → Q(x))) ← (P → ∀ₗ(x ↦ Q(x)))
[∀][→]ᵣ-unmentionedₗ {_}{_}{_} (PaxQx) {x} (P) = PaxQx(P){x}

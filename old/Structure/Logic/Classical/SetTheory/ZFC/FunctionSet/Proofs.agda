module FunctionProofs where
open FunctionSet ⦃ signature ⦄

[∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] : ∀{D : Domain}{P : BinaryRelator} → Proof(∀ₗ(x ↦ ∃ₗ(y ↦ (x ∈ D) ⟶ P(x)(y))) ⟷ ∀ₛ(D)(x ↦ ∃ₗ(y ↦ P(x)(y))))
[∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] {D}{P} = [↔]-with-[∀] ([∃]-unrelatedᵣ-[→])

[∀ₛ∃!]-to[∀ₛ∃] : ∀{P : BinaryRelator}{D : Domain} → Proof(∀ₛ(D)(x ↦ ∃ₗ!(y ↦ P(x)(y)))) → Proof(∀ₛ(D)(x ↦ ∃ₗ(y ↦ P(x)(y))))
[∀ₛ∃!]-to[∀ₛ∃] proof =
  ([∀ₛ]-intro(\{x} → xinD ↦
    [∧].elimₗ([∀ₛ]-elim proof {x} xinD)
  ))

-- The construction of a meta-function in the meta-logic from a function in the set theory
fnset-witness : ∀{D} → (f : Domain) → ⦃ _ : Proof(Total(D)(f)) ⦄ → Function
fnset-witness f ⦃ proof ⦄ = [∃]-fn-witness ⦃ [↔].elimₗ [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] (proof) ⦄

fnset-value : ∀{D} → (f : Domain) → ⦃ proof : Proof(Total(D)(f)) ⦄ → Proof(∀ₛ(D)(x ↦ (x , fnset-witness f(x)) ∈ f))
fnset-value{D} f ⦃ proof ⦄ = [∃]-fn-proof ⦃ [↔].elimₗ [∃]-unrelatedᵣ-[→]ᵣ-inside-[∀ₛ] (proof) ⦄

fnset-proof : ∀{D} → (f : Domain) → ⦃ _ : Proof(FunctionSet(f)) ⦄ → ⦃ total : Proof(Total(D)(f)) ⦄ → Proof(∀ₛ(D)(x ↦ ∀ₗ(y ↦ (fnset-witness{D} f ⦃ total ⦄ x ≡ y) ⟷ ((x , y) ∈ f))))
fnset-proof{D} f ⦃ function ⦄ ⦃ total ⦄ =
  ([∀ₛ]-intro(\{x} → x∈D ↦
    ([∀].intro(\{y} →
      ([↔].intro
        (xy∈f ↦
          ([→].elim
            ([∀].elim([∀].elim([∀].elim function{x}) {fnset-witness f(x)}) {y})
            ([∧].intro
              ([∀ₛ]-elim(fnset-value f) {x} (x∈D))
              (xy∈f)
            )
          )
        )

        (fx≡y ↦
          [≡].elimᵣ (fx≡y) ([∀ₛ]-elim (fnset-value(f)) {x} (x∈D))
        )
      )
    ))
  ))

[→ₛₑₜ]-witness : ∀{A B} → (f : Domain) → ⦃ _ : Proof(f ∈ (A →ₛₑₜ B)) ⦄ → Function
[→ₛₑₜ]-witness f ⦃ proof ⦄ (x) =
  (fnset-witness f
    ⦃ [∧].elimᵣ([∧].elimᵣ([↔].elimᵣ
      ([∀].elim([∀].elim filter-membership))
      (proof)
    )) ⦄
    (x)
  )

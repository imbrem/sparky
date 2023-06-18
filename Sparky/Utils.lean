import Mathlib.Data.Fintype.Card


theorem binary_predicate_pigeonhole
  {α β: Type}
  (P: α -> β -> Prop)
  (I: Infinite { a: α // ∃b: β, P a b })
  (F: Finite { b: β // ∃a: α, P a b })
  : ∃b: β, Infinite { a: α // P a b }
  := 
    have ⟨f, Hf⟩ := @Classical.axiom_of_choice
      { a: α // ∃b: β, P a b }
      (λ_ => { b: β // ∃a: α, P a b })
      (λ⟨a, _⟩ ⟨b, _⟩ => P a b)
      (λ⟨a, b, Hab⟩ => ⟨⟨b, ⟨a, Hab⟩⟩, Hab⟩)
    have ⟨⟨b, ⟨a', Ha'⟩⟩, H⟩ := @Finite.exists_infinite_fiber _ _ I F f;
    ⟨b, 
      @Infinite.of_injective _ _ H 
        (λ⟨⟨a, Ha⟩, Hab⟩ => ⟨a, by
            have Hfa := Hf ⟨a, Ha⟩;
            simp only [] at Hfa;
            generalize Hc: f ⟨a, Ha⟩ = c;
            rw [Hc] at Hfa;
            rw [Hab] at Hc;
            cases Hc
            exact Hfa
          ⟩) 
        (λ⟨_, _⟩ ⟨_, _⟩ => 
          by simp only [Subtype.mk.injEq]; exact Subtype.eq)
      ⟩
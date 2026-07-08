require open Stdlib.Epsilon Logic.Zenon.Main;

symbol Reps a (p : τ a → Prop) : (π (p (ε p)) → π ⊥) → π (∃ p) → π ⊥ ≔
begin
  assume a p peps pex;
  refine peps (εᵢ p pex);
end;

symbol Rnoteps a (p : τ a → Prop) : (π (¬ p (ε (λ x, ¬ p x))) → π ⊥) → π (¬ ∀ (λ x, p x)) → π ⊥ ≔
begin
  assume a p peps pnall;
  refine Rnotall a (λ x, p x) _ pnall;
  assume t pnpt;
  have h : π(`∃ x, ¬ p x) {
    apply ∃ᵢ t pnpt;
};
  refine (εᵢ (λ x, ¬ p x) h (nnpp _ peps));
end;

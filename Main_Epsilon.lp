require open Stdlib.Epsilon;

symbol Reps a (p : τ a → Prop) : (π (p (ε p)) → π ⊥) → π (∃ p) → π ⊥;
symbol Rnoteps a (p : τ a → Prop) : (π (¬ p (ε (λ x, ¬ p x))) → π ⊥) → π (¬ ∀ (λ x, p x)) → π ⊥;

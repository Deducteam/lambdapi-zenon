/* Logic used by the automated theorem prover ZenonModulo
https://github.com/Deducteam/zenon_modulo/tree/modulo */

require open Stdlib.Prop Stdlib.Set Stdlib.Eq Stdlib.FOL;

symbol ι : Set;

symbol select (a:Set) : τ a;

symbol nnpp p : π (¬ ¬ p) → π p;
symbol Rfalse : π ⊥ → π ⊥;
symbol Rnottrue : π (¬ ⊤) → π ⊥;
symbol Raxiom p : π p → π (¬ p) → π ⊥;
symbol Rnoteq a (t : τ a) : π (¬ (t = t)) → π ⊥;
symbol Reqsym a (t u : τ a) : π (t = u) → π (¬ (u = t)) → π ⊥;
symbol Rnotnot p : (π p → π ⊥) → π (¬ ¬ p) → π ⊥;
symbol Rand p q : (π p → π q → π ⊥) → π (p ∧ q) → π ⊥;
symbol Ror p q : (π p → π ⊥) → (π q → π ⊥) → π (p ∨ q) → π ⊥;
symbol Rimply p q : (π (¬ p) → π ⊥) → (π q → π ⊥) → π (p ⇒ q) → π ⊥;
symbol Requiv p q : (π (¬ p) → π (¬ q) → π ⊥) → (π p → π q → π ⊥) → π (p ⇔ q) → π ⊥;
symbol Rnotand p q : (π (¬ p) → π ⊥) → (π (¬ q) → π ⊥) → π (¬ (p ∧ q)) → π ⊥;
symbol Rnotor p q : (π (¬ p) → π (¬ q) → π ⊥) → π (¬ (p ∨ q)) → π ⊥;
symbol Rnotimply p q : (π p → π (¬ q) → π ⊥) → π (¬ (p ⇒ q)) → π ⊥;
symbol Rnotequiv p q : (π (¬ p) → π q → π ⊥) → (π p → π (¬ q) → π ⊥) → π (¬ (p ⇔ q)) → π ⊥;
symbol Rex a p : (Π t : τ a, π (p t) → π ⊥) → π (∃ p) → π ⊥;
symbol Rall a p (t : τ a) : (π (p t) → π ⊥) → π (∀ p) → π ⊥;
symbol Rnotex a p (t : τ a) : (π (¬ (p t)) → π ⊥) → π (¬ (∃ p)) → π ⊥;
symbol Rnotall a p : (Π t : τ a, π (¬ (p t)) → π ⊥) → π (¬ (∀ p)) → π ⊥;
symbol Rsubst a p (t1 t2 : τ a) : (π (¬ (t1 = t2)) → π ⊥) → (π (p t2) → π ⊥) → π (p t1) → π ⊥;
symbol Rconglr a p (t1 t2 : τ a) : (π (p t2) → π ⊥) → π (p t1) → π (t1 = t2) → π ⊥;
symbol Rcongrl a p (t1 t2 : τ a) : (π (p t2) → π ⊥) → π (p t1) → π (t2 = t1) → π ⊥;

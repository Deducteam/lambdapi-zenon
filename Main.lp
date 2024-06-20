/* Logic used by the automated theorem prover ZenonModulo
https://github.com/Deducteam/zenon_modulo/tree/modulo */

require open Logic.U.Prop Logic.U.Set Logic.U.Quant;

// equivalence
symbol ⇔ : Prop → Prop → Prop; notation ⇔ infix right 5;

// equality
symbol = [a] : El a → El a → Prop; notation = infix 12;

// Zenon rules
symbol nnpp p : Prf (¬ ¬ p) → Prf p;
symbol Rfalse : Prf ⊥ → Prf ⊥;
symbol Rnottrue : Prf (¬ ⊤) → Prf ⊥;
symbol Raxiom p : Prf p → Prf (¬ p) → Prf ⊥;
symbol Rnoteq a (t : El a) : Prf (¬ (t = t)) → Prf ⊥;
symbol Reqsym a (t u : El a) : Prf (t = u) → Prf (¬ (u = t)) → Prf ⊥;
symbol Rnotnot p : (Prf p → Prf ⊥) → Prf (¬ ¬ p) → Prf ⊥;
symbol Rand p q : (Prf p → Prf q → Prf ⊥) → Prf (p ∧ q) → Prf ⊥;
symbol Ror p q : (Prf p → Prf ⊥) → (Prf q → Prf ⊥) → Prf (p ∨ q) → Prf ⊥;
symbol Rimply p q : (Prf (¬ p) → Prf ⊥) → (Prf q → Prf ⊥) → Prf (p ⇒ q) → Prf ⊥;
symbol Requiv p q : (Prf (¬ p) → Prf (¬ q) → Prf ⊥) → (Prf p → Prf q → Prf ⊥) → Prf (p ⇔ q) → Prf ⊥;
symbol Rnotand p q : (Prf (¬ p) → Prf ⊥) → (Prf (¬ q) → Prf ⊥) → Prf (¬ (p ∧ q)) → Prf ⊥;
symbol Rnotor p q : (Prf (¬ p) → Prf (¬ q) → Prf ⊥) → Prf (¬ (p ∨ q)) → Prf ⊥;
symbol Rnotimply p q : (Prf p → Prf (¬ q) → Prf ⊥) → Prf (¬ (p ⇒ q)) → Prf ⊥;
symbol Rnotequiv p q : (Prf (¬ p) → Prf q → Prf ⊥) → (Prf p → Prf (¬ q) → Prf ⊥) → Prf (¬ (p ⇔ q)) → Prf ⊥;
symbol Rex a p : (Π t : El a, Prf (p t) → Prf ⊥) → Prf (∃ p) → Prf ⊥;
symbol Rall a p (t : El a) : (Prf (p t) → Prf ⊥) → Prf (∀ p) → Prf ⊥;
symbol Rnotex a p (t : El a) : (Prf (¬ (p t)) → Prf ⊥) → Prf (¬ (∃ p)) → Prf ⊥;
symbol Rnotall a p : (Π t : El a, Prf (¬ (p t)) → Prf ⊥) → Prf (¬ (∀ p)) → Prf ⊥;
symbol Rsubst a p (t1 t2 : El a) : (Prf (¬ (t1 = t2)) → Prf ⊥) → (Prf (p t2) → Prf ⊥) → Prf (p t1) → Prf ⊥;
symbol Rconglr a p (t1 t2 : El a) : (Prf (p t2) → Prf ⊥) → Prf (p t1) → Prf (t1 = t2) → Prf ⊥;
symbol Rcongrl a p (t1 t2 : El a) : (Prf (p t2) → Prf ⊥) → Prf (p t1) → Prf (t2 = t1) → Prf ⊥;

// temporary renamings to be removed ultimately
symbol Type ≔ Set;
symbol ι ≔ ι;
symbol τ ≔ El;
symbol κ ≔ El ι;
symbol ∀α [a] ≔ ∀ [a];
symbol ∃α [a] ≔ ∃ [a];
symbol =α [a] ≔ (=) [a];
symbol ϵ ≔ Prf;

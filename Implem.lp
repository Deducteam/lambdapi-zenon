/* Implementation of Zenon rules in classical FOL. */

require open Stdlib.Prop Stdlib.Set Stdlib.Eq Stdlib.FOL;

symbol Rfalse : π ⊥ → π ⊥ ≔
begin
assume h; apply h
end;

symbol Rnottrue : π (¬ ⊤) → π ⊥ ≔
begin
assume h; refine h _; apply ⊤ᵢ
end;

symbol Raxiom p : π p → π (¬ p) → π ⊥ ≔
begin
assume p hp hnp; apply hnp hp
end;

symbol Rnoteq a (t : τ a) : π (¬ (t = t)) → π ⊥ ≔
begin
assume a t neq; apply neq; reflexivity
end;

symbol Reqsym a (t u : τ a) : π (t = u) → π (¬ (u = t)) → π ⊥ ≔
begin
assume a t u eq neq; apply neq; symmetry; apply eq
end;

symbol Rnotnot p : (π p → π ⊥) → π (¬ ¬ p) → π ⊥ ≔
begin
assume p np nnp; apply nnp np
end;

symbol Rand p q : (π p → π q → π ⊥) → π (p ∧ q) → π ⊥ ≔
begin
assume p q h pq; apply h { apply ∧ₑ₁ pq } { apply ∧ₑ₂ pq }
end;

symbol Ror p q : (π p → π ⊥) → (π q → π ⊥) → π (p ∨ q) → π ⊥ ≔
begin
assume p q np nq pq; apply ∨ₑ pq np nq
end;

symbol Rnotor p q : (π (¬ p) → π (¬ q) → π ⊥) → π (¬ (p ∨ q)) → π ⊥ ≔
begin
assume p q h npq; apply h
{ assume hp; apply npq; apply ∨ᵢ₁ hp }
{ assume hq; apply npq; apply ∨ᵢ₂ hq }
end;

symbol Rex a p : (Π t : τ a, π (p t) → π ⊥) → π (∃ p) → π ⊥ ≔
begin
assume a p h1 h2; apply ∃ₑ h2; assume x px; apply h1 x px
end;

symbol Rall a p (t : τ a) : (π (p t) → π ⊥) → π (`∀ x, p x) → π ⊥ ≔
begin
assume a p t npt h; apply npt; apply h t
end;

symbol Rnotex a p (t : τ a) : (π (¬ (p t)) → π ⊥) → π (¬ (∃ p)) → π ⊥ ≔
begin
assume a p t nnpt h; apply nnpt; assume pt; apply h; apply ∃ᵢ t pt
end;

symbol Rsubst a p (t1 t2 : τ a) : (π (¬ (t1 = t2)) → π ⊥) → (π (p t2) → π ⊥) → π (p t1) → π ⊥ ≔
begin
assume a p t1 t2 nneq npt2 pt1; apply nneq; assume eq; apply npt2;
rewrite left eq; refine pt1
end;

symbol Rconglr a p (t1 t2 : τ a) : (π (p t2) → π ⊥) → π (p t1) → π (t1 = t2) → π ⊥ ≔
begin
assume a p t1 t2 npt2 pt1 eq; apply npt2; rewrite left eq; refine pt1
end;

symbol Rcongrl a p (t1 t2 : τ a) : (π (p t2) → π ⊥) → π (p t1) → π (t2 = t1) → π ⊥ ≔
begin
assume a p t1 t2 npt2 pt1 eq; apply npt2; rewrite eq; refine pt1
end;

symbol Rimply p q : (π (¬ p) → π ⊥) → (π q → π ⊥) → π (p ⇒ q) → π ⊥ ≔
begin
assume p q nnp nq pq; apply nnp; assume hp; apply nq; apply pq; refine hp
end;

symbol Rnotand p q : (π (¬ p) → π ⊥) → (π (¬ q) → π ⊥) → π (¬ (p ∧ q)) → π ⊥ ≔
begin
assume p q nnp nnq npq; apply nnp; assume hp; apply nnq; assume hq; apply npq;
apply ∧ᵢ hp hq
end;

symbol Rnotimply p q : (π p → π (¬ q) → π ⊥) → π (¬ (p ⇒ q)) → π ⊥ ≔
begin
assume p q h1 h2; apply h2; assume hp; apply ⊥ₑ; apply h1 hp;
assume hq; apply h2; assume hp'; refine hq
end;

symbol Rnotequiv p q : (π (¬ p) → π q → π ⊥) → (π p → π (¬ q) → π ⊥) → π (¬ (p ⇔ q)) → π ⊥ ≔
begin
assume p q h1 h2 h3;
have np: π (¬ p)
{ assume hp; apply h2 hp; assume hq; apply h3; apply ∧ᵢ
  { assume hp'; refine hq }
  { assume hq'; refine hp }
};
apply h3; apply ∧ᵢ
{ assume hp; apply ⊥ₑ; apply np hp }
{ assume hq; apply ⊥ₑ; apply h1 np hq }
end;

symbol Requiv p q : (π (¬ p) → π (¬ q) → π ⊥) → (π p → π q → π ⊥) → π (p ⇔ q) → π ⊥ ≔
begin
assume p q h1 h2 eq;
have pq : π (p ⇒ q) { apply ∧ₑ₁ eq };
have qp : π (q ⇒ p) { apply ∧ₑ₂ eq };
have nq: π (¬ q) { assume hq; apply h2 _ hq; apply qp; refine hq };
have np: π (¬ p) { assume hp; apply h2 hp; apply pq; refine hp };
apply h1 np nq
end;

require open Stdlib.Classic;

symbol nnpp p : π (¬ ¬ p) → π p ≔
begin
refine ¬¬ₑ
end;

symbol Rnotall a p : (Π t : τ a, π (¬ (p t)) → π ⊥) → π (¬ (`∀ x, p x)) → π ⊥ ≔
begin
assume a p h1 h2; apply h2; assume t; apply ¬¬ₑ; refine h1 t
end;

symbol Rcut p : (π p → π ⊥) → (π (¬ p) → π ⊥) → π ⊥ ≔
begin
assume p np nnp; apply nnp; assume h; apply np; apply h
end;

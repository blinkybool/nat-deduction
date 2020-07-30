/- Solutions to Chapter 2 exercises
Author: Billy Price
-/

import definitions

namespace nat_deduction

variables {p q r : ℕ}
variable {X : set Form}

example : {p ⟹ q, r ⟹ p, r} ≻ q :=
begin
  apply ⟹E p, assump,
  apply ⟹E r, assump,
  assump
end

example : {p ⟹ q, r ⟹ p} ≻ r ⟹ q :=
begin
  apply ⟹I,
  apply ⟹E p, assump,
  apply ⟹E r, assump,
  assump
end


example : {p ⟹ q} ≻ (r ⟹ p) ⟹ (r ⟹ q) :=
begin
  apply_rules [⟹I],
  apply ⟹E p, assump,
  apply ⟹E r, assump,
  assump
end

example : {p} ≻ q ⟹ (p ⋀ q) :=
begin
  apply ⟹I,
  apply ⋀I; assump
end

example : {p ⋀ (q ⟹ r)} ≻ q ⟹ (p ⋀ r) :=
begin
  apply ⟹I,
  apply ⋀I,
  apply ⋀E₁, assump,
  apply ⟹E q,
  apply ⋀E₂, assump,
  assump
end

variables {A B C : Form}

def and_comm : X ≻ (A ⋀ B ) → X ≻ (B ⋀ A) :=
λ dAB, ⋀I (⋀E₂ _ _ dAB) (⋀E₁ _ _ dAB)

def imp_and : X ≻ A ⟹ B → X ≻ A ⟹ C → X ≻ A ⟹ (B ⋀ C) :=
begin
  intros dAB dAC,
  apply ⟹I,
  apply ⋀I; apply ⟹E A,
  apply WEAK dAB,
  assump,
  apply WEAK dAC,
  assump
end

def imp_trans : X ≻ A ⟹ B → X ≻ B ⟹ C → X ≻ A ⟹ C :=
begin
  intros dAB dBC,
  apply ⟹I,
  apply ⟹E B,
  apply WEAK dBC,
  apply ⟹E A,
  apply WEAK dAB,
  assump
end

def imp_import : X ≻ A ⟹ (B ⟹ C) → X ≻ (A ⋀ B) ⟹ C :=
begin
  intro dABC,
  apply ⟹I,
  apply ⟹E B,
  apply ⟹E A,
  apply WEAK dABC,
  apply ⋀E₁ A B, assump,
  apply ⋀E₂ A B, assump
end

def imp_export : X ≻ (A ⋀ B) ⟹ C → X ≻ A ⟹ (B ⟹ C) :=
begin
  intro dAB_C,
  apply_rules [⟹I],
  apply ⟹E (A ⋀ B),
  rw set.union_assoc,
  apply WEAK dAB_C,
  apply ⋀I; assump
end

def contraction : X ≻ A ⟹ (A ⟹ B) → X ≻ A ⟹ B :=
begin
  intro dAAB,
  apply ⟹I,
  apply ⟹E A,
  apply ⟹E A,
  apply WEAK dAAB,
  all_goals {assump}
end

example : X ∪ {B} ≻ C → X ∪ {A} ≻ B → X ∪ {A} ≻ C :=
begin
  intros dC,
  induction' dC with Y; intro dAB,
  case weakening : { apply ih _ dAB, sorry },
  repeat { sorry }
end

end nat_deduction
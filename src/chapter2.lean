/-
Chapter 2: Connectives: And & If
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
  exact weaken_union_right dAB, 
  assump,
  exact weaken_union_right dAC, 
  assump
end

def imp_trans : X ≻ A ⟹ B → X ≻ B ⟹ C → X ≻ A ⟹ C :=
begin
  intros dAB dBC,
  apply ⟹I,
  apply ⟹E B,
  exact weaken_union_right dBC,
  apply ⟹E A,
  apply weaken_union_right dAB,
  assump
end

def imp_import : X ≻ A ⟹ (B ⟹ C) → X ≻ (A ⋀ B) ⟹ C :=
begin
  intro dABC,
  apply ⟹I,
  apply ⟹E B,
  apply ⟹E A,
  exact weaken_union_right dABC,
  apply ⋀E₁ A B, assump,
  apply ⋀E₂ A B, assump
end

def imp_export : X ≻ (A ⋀ B) ⟹ C → X ≻ A ⟹ (B ⟹ C) :=
begin
  intro dAB_C,
  apply_rules [⟹I],
  apply ⟹E (A ⋀ B),
  rw set.union_assoc,
  exact weaken_union_right dAB_C,
  apply ⋀I; assump
end

def contraction : X ≻ A ⟹ (A ⟹ B) → X ≻ A ⟹ B :=
begin
  intro dAAB,
  apply ⟹I,
  apply ⟹E A,
  apply ⟹E A,
  exact weaken_union_right dAAB,
  all_goals {assump}
end

end nat_deduction
/- Solutions to Chapter 3 exercises
Author: Billy Price
-/

import definitions

namespace nat_deduction

variables {p q r s : ℕ}

example : {p} ≻ ¬¬p :=
begin
  apply ¬I,
  apply ¬E p; assump
end

example : {p ⟹ r, q ⟹ s} ≻ (p ⋀ q) ⟹ (r ⋀ s) :=
begin
  apply ⟹I,
  apply ⋀I,
  { apply ⟹E p, assump,
    apply ⋀E₁ p q, assump },
  { apply ⟹E q, assump,
    apply ⋀E₂ p q, assump }
end

example : {p ⟹ r, q ⟹ s} ≻ (p ⋁ q) ⟹ (r ⋁ s) :=
begin
  apply ⟹I,
  apply ⋁E p q, assump,
  { apply ⋁I₁, apply ⟹E p; assump},
  { apply ⋁I₂, apply ⟹E q; assump}
end

example : {(¬p) ⋁ (¬q)} ≻ ¬(p ⋀ q) :=
begin
  apply ¬I,
  apply ⋁E ¬p ¬q, assump,
  apply ¬E p, assump, apply ⋀E₁ p q, assump,
  apply ¬E q, assump, apply ⋀E₂ p q, assump
end

example : {¬¬¬p} ≻ ¬p :=
begin
  apply ¬I,
  apply ¬E (¬¬p), assump,
  apply ¬I,
  apply ¬E p; assump
end

variable {X : set Form}
variables {A B C : Form}

def explosion (A : Form) {B} : (X ≻ ¬A) → (X ≻ A) → (X ≻ B) :=
begin
  intros dnA dA,
  apply ⊥E,
  apply ¬E A; assumption
end

def distribution : (X ≻ A ⋀ (B ⋁ C)) → (X ≻ (A ⋀ B) ⋁ (A ⋀ C)) :=
begin
  intro dA_BC,
  apply ⋁E B C, exact ⋀E₂ A _ dA_BC,
    { apply ⋁I₁,
      apply ⋀I, 
        { apply ⋀E₁ _ (B ⋁ C),
          apply WEAK dA_BC },
        assump },
    { apply ⋁I₂,
      apply ⋀I, 
        { apply ⋀E₁ _ (B ⋁ C),
          apply WEAK dA_BC },
        assump },
end

def modus_tollens : (X ≻ A ⟹ B) → (X ≻ ¬B) → (X ≻ ¬ A) :=
begin
  intros dAB dnB,
  apply ¬I,
  apply ¬E B, apply WEAK dnB,
  apply ⟹E A, apply WEAK dAB,
  assump
end

def intro_neg_and : (X ≻ ¬A) → (X ≻ ¬(A ⋀ B)) :=
begin
  intro dnA,
  apply ¬I,
  apply ¬E A,
  apply WEAK dnA,
  apply ⋀E₁ A B, assump
end

def or_imp : (X ≻ A ⟹ C) → (X ≻ B ⟹ C) → (X ≻ (A ⋁ B) ⟹ C) :=
begin
  intros dAC dBC,
  apply ⟹I,
  apply ⋁E A B, assump,
  apply ⟹E A, rw set.union_assoc, apply WEAK dAC,
  assump,
  apply ⟹E B, rw set.union_assoc, apply WEAK dBC,
  assump
end

def disjunctive_syllogism : (X ≻ A ⋁ B) → (X ≻ ¬A) → (X ≻ B) :=
begin
  intros dAB dnA,
  apply ⋁E A B dAB,
  { apply ⊥E,
    apply ¬E A,
    apply WEAK dnA,
    assump },
  assump
end

end nat_deduction


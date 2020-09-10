/-
Chapter 4: Facts about Proofs and Provability
Author: Billy Price
-/
import definitions
import tactic.induction

namespace nat_deduction

-- The intuitionistic provability relation on sets of Formulas and Formulas
-- The sole constructor takes a deduction of the appropriate type
inductive provable (X : set Form) (A : Form) : Prop
| mk : X ≻ A → provable

infix ` ⊢I `:60 := provable

variables {A B C : Form}
variables {X Y : set Form}

-- Constructs a non-normalised deduction mimicking the cut rule
def cut_deduction (A : Form) : (X ∪ {A} ≻ B) → (Y ≻ A) → (X ∪ Y ≻ B) :=
begin
  intros XAdB YdA,
  apply ⟹E A,
  apply ⟹I,
    rw [set.union_assoc,
        set.union_comm,
        set.union_assoc,
        set.union_comm _ X],
    exact weaken_union_left XAdB,
  exact weaken_union_left YdA
end

/- The following theorems lift the deduction rules to provability equivalences -/

theorem provable.and_iff : X ⊢I (A ⋀ B) ↔ (X ⊢I A) ∧ (X ⊢I B) :=
begin
  split,
    { rintro ⟨XdAB⟩,
      exact ⟨⟨⋀E₁ _ _ XdAB⟩,⟨⋀E₂ _ _ XdAB⟩⟩ },
    { rintro ⟨⟨XdA⟩,⟨XdB⟩⟩, exact ⟨⋀I XdA XdB⟩ }
end

theorem provable.imp_iff : X ⊢I (A ⟹ B) ↔ X ∪ {A} ⊢I B :=
begin
  split,
    { rintro ⟨XdAB⟩, exact ⟨⟹E A (weaken_union_right XdAB) (by assump)⟩ },
    { rintro ⟨XAdB⟩, exact ⟨⟹I XAdB⟩ }
end

theorem provable.neg_iff : X ⊢I (¬ A) ↔ X ∪ {A} ⊢I ⊥ := provable.imp_iff

theorem provable.explosion : X ⊢I ⊥ → X ⊢I A :=
  λ ⟨XdF⟩, ⟨⊥E XdF⟩

theorem provable.cut {X Y} (A : Form) {B} : X ∪ {A} ⊢I B → Y ⊢I A → X ∪ Y ⊢I B :=
  λ ⟨XAdB⟩ ⟨YdA⟩, by constructor; apply cut_deduction; assumption

theorem proof_from_or_iff : X ∪ {A ⋁ B} ⊢I C ↔ X ∪ {A} ⊢I C ∧ X ∪ {B} ⊢I C :=
begin
  split,
    { rintro ⟨XdAB⟩,
      split; apply provable.cut (A ⋁ B) ⟨XdAB⟩; constructor,
      apply ⋁I₁, assump, apply ⋁I₂, assump },
    { rintro ⟨⟨XdA⟩,⟨XdB⟩⟩, constructor, apply ⋁E A B, assump,
      all_goals {rw [set.union_comm, ←set.union_assoc, set.union_comm _ X], apply weaken_union_right, assumption } }
end

theorem provable.refl {A : Form} : {A} ⊢I A := ⟨by assump⟩

/-- Cuts out the minimal finite set of assumptions needed in any deduction
and produces the compactified proof -/
def compactify {X A} : X ≻ A → { d : Σ X' : finset Form, ↑X' ≻ A // ↑d.1 ⊆ X } :=
begin
  intro dXA,
  induction' dXA,
  case assumption : { use {A}, tidy, assump },
  case and_intro : X A B dXA dXB ih₁ ih₂
    { rcases ih₁ with ⟨⟨X₁, X₁dA⟩⟩,
      rcases ih₂ with ⟨⟨X₂, X₂dB⟩⟩,
      use (X₁ ∪ X₂),
      rw finset.coe_union,
      apply ⋀I,
        { exact weaken_union_right X₁dA }, { rw set.union_comm, exact weaken_union_right X₂dB },
      tidy
    },
  case and_left : { rcases ih with ⟨⟨X', X'dAB⟩⟩, use X', exact ⋀E₁ _ _ X'dAB, tidy },
  case and_right : { rcases ih with ⟨⟨X', X'dAB⟩⟩, use X', exact ⋀E₂ _ _ X'dAB, tidy },
  case imp_intro : X A B
    { rcases ih with ⟨⟨X', X'dB⟩⟩, use X' \ {A};
      simp only [finset.coe_sdiff, finset.coe_singleton] at *,
      apply ⟹I,
      rw set.diff_union_self,
      exact weaken_union_right X'dB,
      rwa [set.diff_subset_iff, set.union_comm] },
  case imp_elim : X A B dXAB dA ihAB ihA
    { rcases ihAB with ⟨⟨X₁, X₁dAB⟩⟩,
      rcases ihA with ⟨⟨X₂, X₂dA⟩⟩,
      use X₁ ∪ X₂; simp [finset.coe_union] at *,
      exact ⟹E A (weaken_union_right X₁dAB) (weaken_union_left X₂dA),
      tidy },  
  case or_left : X A B { rcases ih with ⟨⟨X', X'dA⟩⟩, use X', exact ⋁I₁ X'dA, tidy },
  case or_right : X A B { rcases ih with ⟨⟨X', X'dA⟩⟩, use X', exact ⋁I₂ X'dA, tidy },
  case or_elim : X A B C _ _ _ ih₁ ih₂ ih₃
  {
    rcases ih₁ with ⟨⟨X₁, dX₁AB⟩, sub₁X⟩,
    rcases ih₂ with ⟨⟨X₂, dX₂C⟩, sub₂X⟩,
    rcases ih₃ with ⟨⟨X₃, dX₃C⟩, sub₃X⟩,
    use X₁ ∪ (X₂ \ {A}) ∪ (X₃ \ {B}); simp [finset.coe_union, finset.coe_sdiff, finset.coe_singleton],
    apply ⋁E A B (weaken_union_right dX₁AB),
      { have : ↑X₁ ∪ (↑X₂ \ {A} ∪ ↑X₃ \ {B}) ∪ {A} = ↑X₂ ∪ ({A} ∪ (↑X₃ \ {B} ∪ ↑X₁)),
          { rw [@set.union_assoc Form,
                set.union_assoc _ _ {A},
                set.union_comm _ {A},
                ←set.union_assoc _ {A},
                set.diff_union_self,
                set.union_comm,
                set.union_assoc,
                set.union_assoc] },
        rw this,
        exact weaken_union_right dX₂C },
      { have : ↑X₁ ∪ (↑X₂ \ {A} ∪ ↑X₃ \ {B}) ∪ {B} = ↑X₃ ∪ ({B} ∪ (↑X₁ ∪ ↑X₂ \ {A})),
          { rw [ @set.union_assoc Form,
                  set.union_assoc,
                  set.diff_union_self,
                  ←set.union_assoc,
                  set.union_comm,
                  set.union_assoc ] },
        rw this,
        exact weaken_union_right dX₃C },
    tidy,
  },
  case falsum : { rcases ih with ⟨⟨X',X'dF⟩⟩, use X', apply ⊥E X'dF, tidy },
end

/--Theorem 2 of Chapter 4-/
theorem compactness {X : set Form} {A : Form} : X ⊢I A → ∃ X' : finset Form, ↑X' ⊆ X ∧ ↑X' ⊢I A :=
  λ ⟨XdA⟩, by { rcases compactify XdA with ⟨⟨X', X'dA⟩, X'subX⟩, use X', split, assumption, exact ⟨X'dA⟩ }

/--Definition 11 of Chapter 4-/
def inconsistent (X : set Form) : Prop := X ⊢I ⊥

/- TODO: Formalise detour formulas and detour sequences  - How??? -/

def subformulas : Form → set Form
| ⊥ := {⊥}
| (n : ℕ) := {n}
| (A ⋀ B) := subformulas A ∪ subformulas B ∪ {A ⋀ B}
| (A ⋁ B) := subformulas A ∪ subformulas B ∪ {A ⋁ B}
| (A ⟹ B) := subformulas A ∪ subformulas B ∪ {A ⟹ B}

def subformula (A : Form) := {B : Form // B ∈ subformulas A}

section
open deduction

/--The formulas which *appear* in a written out proof d : X ≻ A
Recursively define as the formulas above the last rule with the conclusion
inserted-/
def deduction.formulas : Π {X A}, X ≻ A → set Form
| X A (assumption mA) := {A}
| X _ (@and_intro _ A B XdA XdB) := deduction.formulas XdA ∪ deduction.formulas XdB ∪ {A ⋀ B}
| X _ (@and_left _ A B XdAB) := deduction.formulas XdAB ∪ {A}
| X _ (@and_right _ A B XdAB) := deduction.formulas XdAB ∪ {B}
| X _ (@imp_intro _ A B XAdB) := deduction.formulas XAdB ∪ {A ⟹ B}
| X B (@imp_elim _ A _ XdAB XdA) := deduction.formulas XdAB ∪ deduction.formulas XdA ∪ {B}
| X _ (@or_left _ A B XdA) := deduction.formulas XdA ∪ {A ⋁ B}
| X _ (@or_right _ A B XdB) := deduction.formulas XdB ∪ {A ⋁ B}
| X C (@or_elim _ A B _ XdAB XAdC XBdC) := deduction.formulas XdAB ∪ deduction.formulas XAdC ∪ deduction.formulas XBdC ∪ {C}
| X A (@falsum _ _ XdF) := deduction.formulas XdF ∪ {A}

end

/--Definition 20-/
def subformula_property {X A} : X ≻ A → Prop := λ XdA, XdA.formulas ⊆ X ∪ {A}

/-- Lemma used in preorder proof-/
lemma provable.premise_contraction {X A B} : X ∪ (X ∪ {A}) ⊢I B → X ∪ {A} ⊢I B := by obviously

/--Any set of formulas induces a preorder on Formulas,-/
instance provable.preorder (X : set Form): preorder Form :=
{ le := λ A B, X ∪ {A} ⊢I B,
  lt := λ A B, X ∪ {A} ⊢I B ∧ ¬ (X ∪ {B} ⊢I A),
  le_refl := λ A, ⟨by assump⟩,
  le_trans := λ A B C ApB BpC, provable.premise_contraction $ provable.cut B BpC ApB,
  lt_iff_le_not_le := λ A B, by refl }

/- Chapter 6 Exercises -/
section exercises

variables {p q r : ℕ}

/-Question 1-/

example : inconsistent {p,q,¬(p ⋀ q)} :=
  ⟨¬E (p ⋀ q) (by assump) (by apply ⋀I; assump)⟩

-- TODO: finish chapter 4 exercises

end exercises



end nat_deduction
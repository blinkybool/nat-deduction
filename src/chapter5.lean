/-
Chapter 5: Models & Counter Examples
Author: Billy Price
-/
import definitions chapter4
import data.finset

namespace nat_deduction

/-- A model is uniquely determined by its valuation of atoms-/
@[reducible]
def Model := finset ℕ

/-- The evaluation of a Model on a formula -/
@[simp]
def Form.eval_model (M : Model) : Form → bool
| ⊥         := ff
| (n : ℕ)   := n ∈ M
| (A ⋀ B)   := Form.eval_model A && Form.eval_model B
| (A ⋁ B)   := Form.eval_model A || Form.eval_model B
| (A ⟹ B) := (bnot $ Form.eval_model A) || Form.eval_model B

notation M`[`A`]` := Form.eval_model M A

/--sat M X means M evaluates to true on every formula in X-/
def sat (M : Model) (X : set Form) : Prop := ∀ A ∈ X, M[A] = tt

-- Some simplification theorems, so that something like
-- sat M {A,B,C} simplifies to M[A] = tt ∧ M[B] = tt ∧ M[C] = tt

@[simp]
theorem sat_insert {M : Model} {X : set Form} {A : Form} :
  sat M (insert A X) ↔ M[A] = tt ∧ sat M X := set.ball_insert_iff

@[simp]
theorem sat_singleton {M : Model} {A : Form} :
  sat M {A} ↔ M[A] = tt :=
by split; tidy

@[simp]
theorem sat_empty {M : Model} : sat M ∅ :=
begin
  intros A mem, simp at *, contradiction
end

@[simp]
theorem sat_union {M : Model} {X Y : set Form} : sat M (X ∪ Y) ↔ (sat M X ∧ sat M Y) :=
begin
  split,
    intro satXY,
    split;
    intros A Amem;
    apply satXY,
    exact set.mem_union_left _ Amem,
    exact set.mem_union_right _ Amem,
  rintro ⟨satX, satY⟩, tidy
end

/-- The type of counterexamples of an argument X ≻ A-/
def counterexample (X : set Form) (A : Form) := {M // sat M X ∧ M[A] = ff}

/-- Validity according to boolean models-/
def boolean.valid (X : set Form) (A : Form) : Prop := ∀ M : Model, (sat M X → M[A] = tt)
@[reducible]
def boolean.invalid (X : set Form) (A : Form) : Prop := ¬ (boolean.valid X A)

infix ` ⊨ `:60 := boolean.valid
infix ` ⊭ `:60 := boolean.invalid

/-- Boolean unsatisfiability of a set X of formulas -/
def unsat (X : set Form) : Prop := X ⊨ ⊥

/--The textbooks definition of validity (the right side of this equivalence)
is inconvenient to work with, this theorem proves the equivalence-/
theorem boolean.valid_iff_no_counterexample (X : set Form) (A : Form) : X ⊨ A ↔ ¬ ∃ M, sat M X ∧ M[A] = ff :=
begin
  split,
    rintros h ⟨M,hX,hnA⟩,
    apply absurd hnA, simp,
    exact h M hX,
  intros hA N NsatX,
  by_contradiction nA,
  apply hA,
  use N, tidy,
end

/-- Any counterexample gives a proof of invalidity -/
def invalid_of_counterexample {X : set Form} {A : Form} : counterexample X A → X ⊭ A :=
begin
  rintro ⟨M, MX, MA⟩,
  intro valid,
  apply absurd MA, simp,
  exact valid M MX
end

end nat_deduction

meta def tactic.interactive.by_counterexample : tactic unit :=
  do `[apply nat_deduction.invalid_of_counterexample]

namespace nat_deduction

section

variables {X Y : set Form}
variables {A B C : Form}


theorem boolean.valid_refl : {A} ⊨ A :=
begin
  intros _ _, simp * at *,
end

theorem boolean.valid_weakening : X ⊨ A → X ∪ Y ⊨ A :=
begin
  intros XbA M MsatA,
  apply XbA,
  simp * at *,
end

theorem boolean.valid_cut (A : Form) : X ⊨ A → Y ∪ {A} ⊨ B → X ∪ Y ⊨ B :=
begin
  intros XbA YAbB M MsatXY,
  apply YAbB, simp * at *,
  apply XbA, tidy,
end

theorem boolean.compactness : X ⊨ A → ∃ X' : finset Form, ↑X' ⊆ X ∧ ↑X' ⊨ A := sorry

theorem boolean.and_iff : X ⊨ A ⋀ B ↔ X ⊨A ∧ X ⊨ B :=
begin
  split,
    intro hAB,
    split;
    intros M MsatX;
    specialize hAB M MsatX; simp * at *,
  rintro ⟨hA,hB⟩,
  intros M MsatX,
  specialize hA M MsatX,
  specialize hB M MsatX,
  simp * at *
end

theorem boolean.imp_iff : X ⊨ A ⟹ B ↔ X ∪ {A} ⊨ B :=
begin
  split,
    intros XbAB M Msat, simp at *,
    specialize XbAB M Msat.2,
    simp * at *,
  intros XAbB M Msat, simp at *,
  specialize XAbB M,
  by_cases (M[A] = tt),
    apply or.inr,
    apply XAbB,
    simp, split; assumption,
  simp at *, exact or.inl (by assumption)
end

theorem boolean.from_or_iff : X ∪ {A ⋁ B} ⊨ C ↔ (X ∪ {A} ⊨ C ∧ X ∪ {B} ⊨ C) :=
begin
  split,
    intro XABbC, split; intros M Msat; apply XABbC; simp * at *,
  rintros ⟨XAbC,XBbC⟩ M Msat,
  specialize XAbC M,
  specialize XBbC M,
  simp * at *, tidy,
end

end

section chapter_5_basic_questions

variables {p q r : ℕ}
variables {X : set Form}
variables {A B : Form}

example {q ≠ p}: {¬(p ⋀ q)} ⊭ (¬p) ⋀ (¬q) :=
begin
  by_counterexample,
  use {p}, simp * at *
end

example : {p ⟹ q, q ⟹ r} ⊨ p ⟹ r :=
begin
  intros M Msat, simp * at *,
  cases Msat.1 with hnp hq,
  exact or.inl hnp,
  cases Msat.2 with hnq hr,
  contradiction,
  exact or.inr hr
end

example {h : p ≠ q ∧ p ≠ r} : {p ⟹ q, q ⟹ r} ⊭ ¬p ⟹ ¬r :=
begin
  by_counterexample,
  use {q,r}, simp * at *
end

example : {¬ (p ⟹ q)} ⊨ p :=
  by intros _ _; simp * at *

example : {¬ (p ⋀ q)} ⊨ (¬ p) ⋁ (¬ q) :=
  by intros M Msat; simp * at *

example : ∅ ⊨ ((p ⟹ q) ⟹ p) ⟹ p :=
begin
  intros M Msat, simp * at *,
  by_cases p ∈ M; simp *
end

-- Question 3

-- If A ⊨ B then ¬ B ⊨ ¬ A
theorem boolean.contrapositive : {A} ⊨ B → {¬B} ⊨ ¬A :=
begin
  intros AbB M Msat,
  by_contradiction h,
  specialize AbB M,
  simp at *,
  specialize AbB h,
  apply absurd Msat, simp * at *
end

-- If A ⊨ B then its not true that B ⊨ A
-- False, take A = B
example : ⊥ ⊨ ⊥ → ⊥ ⊨ ⊥ := id

-- Either A ⊨ B or B ⊨ A
-- False (with disinct atoms)
example {h : p ≠ q} : ¬ ({p} ⊨ q ∨ {q} ⊨ p) :=
begin
  suffices : ∀ {a b : ℕ}, a ≠ b → {a} ⊭ b,
    rintro (hpq | hqp),
    apply this (by assumption) hpq,
    apply this (by symmetry;assumption) hqp,
  intros a b anb,
  by_counterexample, use {a}, tidy
end

theorem boolean.contract_pos_to_neg : X ∪ {A} ⊨ ¬A ↔ X ⊨ ¬A :=
begin
  split,
    intros XAbnA M Msat,
    specialize XAbnA M,
    simp * at *, { cases M[A], tidy, },
  intros XbnA M Msat, simp * at *,
  apply absurd XbnA,
  by_counterexample, use M, tidy
end

-- X ⊨ A ⋁ B iff X ⊨ A or X ⊨ B
-- False
example {h : p ≠ q}: ¬ ({p ⋁ q} ⊨ p ⋁ q ↔ (({p ⋁ q} ⊨ p) ∨ ({p ⋁ q} ⊨ q))) :=
begin
  intro h,
  cases h.1 (boolean.valid_refl) with k₁ k₂,
  apply absurd k₁,
  by_counterexample, use {q}, simp * at *,
  apply absurd k₂,
  by_counterexample, use {p}, simp * at *, tidy
end

/-TODO: Question 4-/

/-TODO: Challenge Questions-/


end chapter_5_basic_questions


end nat_deduction
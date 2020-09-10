import definitions

namespace nat_deduction

/-- Inductive definition of a classical deduction X ≻ A (argument) from a set of Formulas X
to a Formula A. This the same as the definition of a deduction + a double-negation elimination rule. -/
inductive classical.deduction : set Form → Form → Type
| assumption {X} {A}       : (A ∈ X) → classical.deduction X A
| and_intro  {X} {A B}     : classical.deduction X A → classical.deduction X B → classical.deduction X (A ⋀ B)
| and_left   {X} (A B)     : classical.deduction X (A ⋀ B) → classical.deduction X A
| and_right  {X} (A B)     : classical.deduction X (A ⋀ B) → classical.deduction X B
-- note X may or may not contain A, which corresponds to the ability to
-- discharge formulas which are no longer assumptions (or not).
| imp_intro  {X} {A B}     : classical.deduction (X ∪ {A}) B → classical.deduction X (A ⟹ B)
| imp_elim   {X} (A) {B}   : classical.deduction X (A ⟹ B) → classical.deduction X A → classical.deduction X B
| or_left    {X} {A B}     : classical.deduction X A → classical.deduction X (A ⋁ B)
| or_right   {X} {A B}     : classical.deduction X B → classical.deduction X (A ⋁ B)
| or_elim    {X} (A B) {C} : classical.deduction X (A ⋁ B) → classical.deduction (X ∪ {A}) C → classical.deduction (X ∪ {B}) C → classical.deduction X C
| falsum     {X} {A}       : classical.deduction X ⊥ → classical.deduction X A
| dne        {X} {A}       : classical.deduction X ¬¬A → classical.deduction X A

-- Notation for deduction types
infix ` ≻* `:60 := classical.deduction

def classical.weakening {X Y A} : X ⊆ Y → X ≻* A → Y ≻* A :=
begin
  intros hXY XdA,
  induction' XdA with X,
  case assumption : {exact classical.deduction.assumption (hXY h)},
  case and_intro : X A B _ _ ih₁ ih₂
    { apply classical.deduction.and_intro,
      exact ih₁ hXY,
      exact ih₂ hXY },
  case and_left : X A B ih
    { apply classical.deduction.and_left, exact ih hXY },
  case and_right : X A B ih
    { apply classical.deduction.and_right, exact ih hXY },
  case imp_intro : X A B _ ih
    { apply classical.deduction.imp_intro,
      apply ih, exact set.union_subset_union_left {A} hXY },
  case imp_elim : X A B _ _ ih₁ ih₂
    { apply classical.deduction.imp_elim,
      exact ih₁ hXY,
      exact ih₂ hXY },
  case or_left : X A B _ ih
    { apply classical.deduction.or_left, exact ih hXY },
  case or_right : X A B _ ih
    { apply classical.deduction.or_right, exact ih hXY },
  case or_elim : X A B C _ _ _ ih ihA ihB {
    apply classical.deduction.or_elim,
    apply ih hXY,
    apply ihA, exact set.union_subset_union_left _ hXY,
    apply ihB, exact set.union_subset_union_left _ hXY },
  case falsum : X A _ ih { apply classical.deduction.falsum, exact ih hXY },
  case dne : X A { apply classical.deduction.dne, exact ih hXY }
end

def classical.weaken_union_left {Y X A} : X ≻ A → Y ∪ X ≻ A
  := λ XdA, deduction.weakening (set.subset_union_right Y X) XdA

def classical.weaken_union_right {Y X A} : X ≻ A → X ∪ Y ≻ A
  := λ XdA, deduction.weakening (set.subset_union_left X Y) XdA

-- Derived rules for negation
def classical.deduction.neg_intro {X A}: X ∪ {A} ≻* ⊥ → X ≻* ¬A := classical.deduction.imp_intro
def classical.deduction.neg_elim {X} (A) : X ≻* ¬A → X ≻* A → X ≻* ⊥ := classical.deduction.imp_elim A

-- Derived rules which commute set unions
def classical.deduction.imp_intro' {X A B} : ({A} ∪ X) ≻* B → X ≻* (A ⟹ B) := by {rw set.union_comm, exact classical.deduction.imp_intro}

-- Shorthand for deduction rules
notation `⋀I*` := classical.deduction.and_intro
notation `⋀E₁*` := classical.deduction.and_left
notation `⋀E₂*` := classical.deduction.and_right
notation `⟹I*` := classical.deduction.imp_intro
notation `⟹I*'` := classical.deduction.imp_intro'
notation `⟹E*` := classical.deduction.imp_elim
notation `⋁E*` := classical.deduction.or_elim
notation `⋁I₁*` := classical.deduction.or_left
notation `⋁I₂*` := classical.deduction.or_right
notation `⊥E*` := classical.deduction.falsum
notation `¬I*` := classical.deduction.neg_intro
notation `¬E*` := classical.deduction.neg_elim
notation `DNE` := classical.deduction.dne

def classical.deduction.excluded_middle {X A} : X ≻* (A ⋁ ¬A) :=
begin
  apply @classical.weakening ∅, exact set.empty_subset X,
  apply DNE,
  apply ¬I*,
  apply ¬E* (A ⋁ ¬A),
    { apply classical.deduction.assumption, obviously },
  apply ⋁I₂*,
  apply ¬I*,
  apply ¬E* (A ⋁ ¬A),
    { apply classical.deduction.assumption, obviously },
  apply ⋁I₁*,
  apply classical.deduction.assumption, obviously
end

notation `LEM` := classical.deduction.excluded_middle

end nat_deduction

/-- A tactic to produce a deduction of something like `X ∪ {A} ≻ A`,
via the assumption rule and an automated proof of `A ∈ X ∪ {A}`
-/ 
meta def tactic.interactive.assumpc : tactic unit :=
  do `[apply nat_deduction.classical.deduction.assumption _; obviously]
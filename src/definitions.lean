/-
Foundational definitions for natural deduction
(Mostly from Chapter 2)
Author: Billy Price
-/
import tactic
import tactic.induction

namespace nat_deduction

/-- The type of Formulas, defined inductively
-/
@[derive decidable_eq]
inductive Form : Type
-- The absurdity, ⊥
| bot : Form
-- Atomic Formulas are introduced via natural numbers (atom 0, atom 1, atom 2)
| atom : ℕ → Form
-- conjunction
| and : Form → Form → Form
-- disjunction
| or  : Form → Form → Form
-- implication
| imp : Form → Form → Form

-- we define `¬A` as `A ⟹ ⊥` (makes proofs smaller)
@[reducible]
def Form.neg (A : Form) : Form := Form.imp A Form.bot

/--
We now define notation and coercions for nicer looking formulas
-/

-- Coerce natural numbers to Formulas as atoms
-- Given p : ℕ, just write `p` or `↑p` instead of `atom p`
-- (`↑p` forces the coercion)
instance nat_coe_Form : has_coe ℕ Form := ⟨Form.atom⟩

infix ` ⋀ `:75 := Form.and
infix ` ⋁ `:74 := Form.or
infix ` ⟹ `:75 := Form.imp
notation `⊥` := Form.bot
prefix `¬` := Form.neg
notation `⊤` := ¬⊥ -- the simplest tautology

open Form

-- Now we recursively define the number of connectives in a formula
def complexity : Form → ℕ
| bot           := 0
| (n : ℕ)       := 0
| (A ⋀ B)       := (complexity A + complexity B) + 1
| (A ⋁ B)       := (complexity A + complexity B) + 1
| (A ⟹ B)      := (complexity A + complexity B) + 1

/-- Inductive definition of a deduction X ≻ A (argument) from a set of Formulas X
to a Formula A. This is equivalent to the usual proof tree presentation, however,
there is no need to "discharge" Formulas - we just choose to keep them as assumptions
or not. This forces us to add a weakening rule to the usual collection of rules.
-/
inductive deduction : set Form → Form → Type
| assumption {X} {A}       : (A ∈ X) → deduction X A
| and_intro  {X} {A B}     : deduction X A → deduction X B → deduction X (A ⋀ B)
| and_left   {X} (A B)     : deduction X (A ⋀ B) → deduction X A
| and_right  {X} (A B)     : deduction X (A ⋀ B) → deduction X B
-- note X may or may not contain A, which corresponds to the ability to
-- discharge formulas which are no longer assumptions (or not).
| imp_intro  {X} {A B}     : deduction (X ∪ {A}) B → deduction X (A ⟹ B)
| imp_elim   {X} (A) {B}   : deduction X (A ⟹ B) → deduction X A → deduction X B
| or_left    {X} {A B}     : deduction X A → deduction X (A ⋁ B)
| or_right   {X} {A B}     : deduction X B → deduction X (A ⋁ B)
| or_elim    {X} (A B) {C} : deduction X (A ⋁ B) → deduction (X ∪ {A}) C → deduction (X ∪ {B}) C → deduction X C
| falsum     {X} {A}       : deduction X ⊥ → deduction X A

-- Notation for deduction types
infix ` ≻ `:60 := deduction

def deduction.weakening {X Y A} : X ⊆ Y → X ≻ A → Y ≻ A :=
begin
  intros hXY XdA,
  induction' XdA with X,
  case assumption : {exact deduction.assumption (hXY h)},
  case and_intro : X A B _ _ ih₁ ih₂
    { apply deduction.and_intro,
      exact ih₁ hXY,
      exact ih₂ hXY },
  case and_left : X A B ih
    { apply deduction.and_left, exact ih hXY },
  case and_right : X A B ih
    { apply deduction.and_right, exact ih hXY },
  case imp_intro : X A B _ ih
    { apply deduction.imp_intro,
      apply ih, exact set.union_subset_union_left {A} hXY },
  case imp_elim : X A B _ _ ih₁ ih₂
    { apply deduction.imp_elim,
      exact ih₁ hXY,
      exact ih₂ hXY },
  case or_left : X A B _ ih
    { apply deduction.or_left, exact ih hXY },
  case or_right : X A B _ ih
    { apply deduction.or_right, exact ih hXY },
  case or_elim : X A B C _ _ _ ih ihA ihB {
    apply deduction.or_elim,
    apply ih hXY,
    apply ihA, exact set.union_subset_union_left _ hXY,
    apply ihB, exact set.union_subset_union_left _ hXY },
  case falsum : X A _ ih { apply deduction.falsum, exact ih hXY }
end

def weaken_union_left {Y X A} : X ≻ A → Y ∪ X ≻ A
  := λ XdA, deduction.weakening (set.subset_union_right Y X) XdA

def weaken_union_right {Y X A} : X ≻ A → X ∪ Y ≻ A
  := λ XdA, deduction.weakening (set.subset_union_left X Y) XdA

-- Derived rules for negation
def deduction.neg_intro {X A}: X ∪ {A} ≻ ⊥ → X ≻ ¬A := deduction.imp_intro
def deduction.neg_elim {X} (A) : X ≻ ¬A → X ≻ A → X ≻ ⊥ := deduction.imp_elim A

-- Derived rules which commute set unions
def deduction.imp_intro' {X A B} : {A} ∪ X ≻ B → X ≻ A ⟹ B := by {rw set.union_comm, exact deduction.imp_intro}
-- def deduction.weakening' {X A Y} : X ≻ A → Y ∪ X ≻ A := by {rw set.union_comm, exact deduction.weakening}

-- Shorthand for deduction rules
notation `⋀I` := deduction.and_intro
notation `⋀E₁` := deduction.and_left
notation `⋀E₂` := deduction.and_right
notation `⟹I` := deduction.imp_intro
notation `⟹I'` := deduction.imp_intro'
notation `⟹E` := deduction.imp_elim
notation `⋁E` := deduction.or_elim
notation `⋁I₁` := deduction.or_left
notation `⋁I₂` := deduction.or_right
notation `⊥E` := deduction.falsum
notation `¬I` := deduction.neg_intro
notation `¬E` := deduction.neg_elim

end nat_deduction

/-- A tactic to produce a deduction of something like `X ∪ {A} ≻ A`,
via the assumption rule and an automated proof of `A ∈ X ∪ {A}`
-/ 
meta def tactic.interactive.assump : tactic unit :=
  do `[apply nat_deduction.deduction.assumption _; obviously]
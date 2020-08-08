import data.finset
import tactic

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
| weakening  {X} {A Y}     : deduction X A → deduction (X ∪ Y) A
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

-- Derived rules for negation
def deduction.neg_intro {X A}: X ∪ {A} ≻ ⊥ → X ≻ ¬A := deduction.imp_intro
def deduction.neg_elim {X} (A) : X ≻ ¬A → X ≻ A → X ≻ ⊥ := deduction.imp_elim A

-- Derived rules which commute set unions
def deduction.imp_intro' {X A B} : deduction ({A} ∪ X) B → deduction X (A ⟹ B) := by {rw set.union_comm, exact deduction.imp_intro}
def deduction.weakening' {X A Y} : deduction X A → deduction (Y ∪ X) A := by {rw set.union_comm, exact deduction.weakening}

-- Shorthand for deduction rules
notation `WEAK` := deduction.weakening
notation `WEAK'` := deduction.weakening'
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
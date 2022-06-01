import tactic

inductive MForm (α : Type)
-- The absurdity, ⊥
| bot : MForm
-- Atomic MFormulas are introduced via α
| atom : α → MForm
-- conjunction
| and : MForm → MForm → MForm
-- disjunction
| or  : MForm → MForm → MForm
-- implication
| imp : MForm → MForm → MForm
-- possibility
| pos : MForm → MForm
-- necessity
| nec : MForm → MForm

variable {α : Type}

-- we define `¬A` as `A ⟹ ⊥` (makes proofs smaller)
@[reducible]
def MForm.neg (A : MForm α) : MForm α := MForm.imp A MForm.bot

-- Coerce atoms type objects to Formulas
-- Given p : ℕ, just write `p` or `↑p` instead of `atom p`
-- (`↑p` forces the coercion)
instance nat_coe_MForm : has_coe α (MForm α) := ⟨MForm.atom⟩

infix ` ⋀ `:75 := MForm.and
infix ` ⋁ `:74 := MForm.or
infix ` ⟹ `:75 := MForm.imp
prefix `¬` := MForm.neg
prefix `◇`:76 := MForm.pos
prefix `□`:76 := MForm.nec

instance MForm_has_bot : has_bot (MForm α) := ⟨MForm.bot⟩


inductive necessitive : MForm α → Prop
| mk_nec {A} : necessitive □A
| mk_neg_pos {A} : necessitive ¬◇A

inductive modal : MForm α → Prop
| mk_nec {A} : modal □A
| mk_pos {A} : modal ◇A
| mk_neg_nec {A} : modal ¬□A
| mk_neg_pos {A} : modal ¬◇A

@[simp]
theorem modal_insert {X : set (MForm α)} {A : MForm α} :
  (∀ B ∈ (insert A X), modal B) ↔ (modal A ∧ ∀ B ∈ X, modal B) := set.ball_insert_iff

@[simp]
theorem modal_singleton {α : Type} {A : MForm α} :
  (∀ B : MForm α, B ∈ ({A} : set (MForm α)) →  @modal α B) ↔ modal A := by simp;refl

@[simp]
theorem necessitive_insert {X : set (MForm α)} {A : MForm α} :
  (∀ B ∈ (insert A X), necessitive B) ↔ (necessitive A ∧ ∀ B ∈ X, necessitive B) := set.ball_insert_iff

@[simp]
theorem necessitive_singleton {A : MForm α} :
  (∀ B : MForm α, B ∈ ({A} : set (MForm α)) →  @necessitive α B) ↔ necessitive A := by simp;refl

/-- Inductive definition of a S5.deduction X ≻ A (argument) from a set of Formulas X
to a Formula A. This is equivalent to the usual proof tree presentation, however,
there is no need to "discharge" Formulas - we just choose to keep them as assumptions
or not. This forces us to add a weakening rule to the usual collection of rules.
-/
inductive S5.deduction : set (MForm α) → (MForm α) → Type
| assumption  {X} {A}           : (A ∈ X) → S5.deduction X A
| and_intro   {X Y} {A B}       : S5.deduction X A → S5.deduction Y B → S5.deduction (X ∪ Y) (A ⋀ B)
| and_left    {X} (A B)         : S5.deduction X (A ⋀ B) → S5.deduction X A
| and_right   {X} (A B)         : S5.deduction X (A ⋀ B) → S5.deduction X B
| imp_intro   {X} {A B}         : S5.deduction (X ∪ {A}) B → S5.deduction X (A ⟹ B)
| imp_elim    {X Y} (A) {B}     : S5.deduction X (A ⟹ B) → S5.deduction Y A → S5.deduction (X ∪ Y) B
| or_left     {X} {A B}         : S5.deduction X A → S5.deduction X (A ⋁ B)
| or_right    {X} {A B}         : S5.deduction X B → S5.deduction X (A ⋁ B)
| or_elim     {X Y Z} (A B) {C} : S5.deduction X (A ⋁ B) → S5.deduction (Y ∪ {A}) C → S5.deduction (Z ∪ {B}) C → S5.deduction (X ∪ Y ∪ Z) C
| falsum_elim {X} {A}           : S5.deduction X ⊥ → S5.deduction X A
| dne         {X} {A}           : S5.deduction X (¬¬A) → S5.deduction X A
| nec_intro   {X} (Y) {A}       : (∀ B ∈ Y, modal B) → Y ⊆ X → S5.deduction Y A → S5.deduction X □A
| nec_elim    {X} {A}           : S5.deduction X □A → S5.deduction X A
| pos_intro   {X} {A}           : S5.deduction X A → S5.deduction X ◇A
| pos_elim    {X} (Y) (A)         : (∀ B ∈ Y, modal B) → S5.deduction X ◇A → S5.deduction (Y ∪ {A}) ⊥  → S5.deduction (X ∪ Y) ⊥

-- Notation for deduction types with natural number atoms
infix ` ≻₅ `:60 := S5.deduction

-- Derived rules for negation
def S5.deduction.neg_intro {X} {A : MForm α} : (X ∪ {A}) ≻₅ ⊥ → X ≻₅ ¬A := S5.deduction.imp_intro
def S5.deduction.neg_elim {X Y} (A : MForm α) : X ≻₅ ¬A → Y ≻₅ A → X ∪ Y ≻₅ ⊥ := S5.deduction.imp_elim A
def S5.deduction.imp_elim' {X} (A : MForm α) {B} : X ≻₅ (A ⟹ B) → X ≻₅ A → X ≻₅ B :=
  λ h k, by { convert S5.deduction.imp_elim _ h k, tidy}
def S5.deduction.neg_elim' {X} (A : MForm α) : X ≻₅ ¬A → X ≻₅ A → X ≻₅ ⊥ := S5.deduction.imp_elim' A
def S5.deduction.and_intro' {X} (A : MForm α) {B} : X ≻₅ A → X ≻₅ B → X ≻₅ A ⋀ B :=
  λ h k, by { convert S5.deduction.and_intro h k, tidy}
def S5.deduction.or_elim' {X} (A B : MForm α) {C} : X ≻₅ A ⋁ B → X ∪ {A} ≻₅ C → X ∪ {B} ≻₅ C → X ≻₅ C :=
  λ h j k, by { convert S5.deduction.or_elim A B h j k, tidy }

def S5.deduction.nec_intro' {X} {A : MForm α} : (∀ B ∈ X, modal B) → X ≻₅ A → X  ≻₅ □A :=
  λ mX h, S5.deduction.nec_intro X mX set.subset.rfl h

notation `⋀I` := S5.deduction.and_intro
notation `⋀I'` := S5.deduction.and_intro'
notation `⋀E₁` := S5.deduction.and_left
notation `⋀E₂` := S5.deduction.and_right
notation `⟹I` := S5.deduction.imp_intro
notation `⟹E` := S5.deduction.imp_elim
notation `⟹E'` := S5.deduction.imp_elim'
notation `⋁E` := S5.deduction.or_elim
notation `⋁E'` := S5.deduction.or_elim'
notation `⋁I₁` := S5.deduction.or_left
notation `⋁I₂` := S5.deduction.or_right
notation `⊥E` := S5.deduction.falsum
notation `¬I` := S5.deduction.neg_intro
notation `¬E` := S5.deduction.neg_elim
notation `¬E'` := S5.deduction.neg_elim'
notation `DNE` := S5.deduction.dne
notation `□I` := S5.deduction.nec_intro
notation `□I'` := S5.deduction.nec_intro'
notation `□E` := S5.deduction.nec_elim
notation `◇I` := S5.deduction.pos_intro
notation `◇E` := S5.deduction.pos_elim

structure pwm (α W : Type) :=
(worlds : set W)
(val : α → W → bool)

-- def models {α W} (M : pwm α W) : Π (w ∈ M.worlds), MForm α → Prop
-- | w _ ⊥ := false
-- | w h (p : α) := M.val p w = tt
-- | w h (A ⋀ B) := models w h A ∧ models w h B
-- | w h (A ⋁ B) := models w h A ∨ models w h B
-- | w h (A ⟹ B) := models w h A → models w h B
-- | _ _ (◇A) := ∃ u ∈ M.worlds, models u (by assumption) A 
-- | _ _ (□A) := ∀ u ∈ M.worlds, models u (by assumption) A

-- def countermodel {α W} (X : set (MForm α)) (A : MForm α) :=
-- {C : pwm α W × W   // C.2 ∈ C.1.worlds ∧ (∀ F ∈ X, models M w (by assumption) F) ∧  }

-- structure countermodel {α β : Type} (X : set (MForm α)) (A : MForm α) extends model α β :=
-- (cw : β)
-- (cw_here : cw ∈ worlds)
-- (premises_true : ∀ F ∈ X, models )
-- (conclustion_false : ∀ F ∈ X, val )


/-- A tactic to produce a deduction of something like `X ∪ {A} ≻ A`,
via the assumption rule and an automated proof of `A ∈ X ∪ {A}`
-/ 
meta def tactic.interactive.assump : tactic unit :=
  do `[apply S5.deduction.assumption _; obviously]


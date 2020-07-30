/- Chapter 4: Formalising Provability
Author: Billy
-/
import definitions

namespace nat_deduction

inductive provable (X : set Form) (A : Form) : Prop
| mk : X ≻ A → provable

infix ` ⊢I `:60 := provable


variables {A B C : Form}
variables {X Y : set Form}

def cut_deduction (A : Form) : (X ∪ {A} ≻ B) → (Y ≻ A) → (X ∪ Y ≻ B) := sorry
-- begin
--   intro YAdB,
--   suffices : ∀ {X Y}, (Y ≻ A) → (X ∪ Y ≻ B), exact this,
--   induction' YAdB,
--   case weakening : X' B X'subYA XdB { intros X Y, apply ih, sorry, sorry},
--   case assumption : B elem { intros X Y, sorry },
--   case and_intro : B C _ _ ihB ihC { intros X Y XdA, apply ⋀I, apply ihB, assumption, apply ihC, assumption, },
--   repeat {sorry}
-- end

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
    { rintro ⟨XdAB⟩,
      constructor,
      apply ⟹E A,
      apply WEAK XdAB,
      assump},
    { rintro ⟨XAdB⟩, exact ⟨⟹I XAdB⟩ }
end

theorem provable.neg_iff : X ⊢I (¬ A) ↔ X ∪ {A} ⊢I ⊥ := provable.imp_iff

theorem provable.weakening (Y : set Form) : X ⊢I A → X ∪ Y ⊢I A :=
  λ ⟨XdA⟩, ⟨WEAK XdA⟩

theorem proof_from_or_iff : X ∪ {A ⋁ B} ⊢I C ↔ X ∪ {A} ⊢I C ∧ X ∪ {B} ⊢I C := sorry
-- begin
--   split,
--     { rintro ⟨XABdC⟩,
--       split;constructor;
--       apply cut_deduction (A ⋁ B) XABdC,
--       apply ⋁I₁, assump,
--       apply ⋁I₂, assump
--       },
--     { rintro ⟨⟨XAdC⟩,⟨XBdC⟩⟩, constructor,
--       apply ⋁E A B, assump,
--       rw [set.union_assoc, set.union_comm _ {A}, ←set.union_assoc],
--       apply WEAK XAdC,
--       rw [set.union_assoc, set.union_comm _ {B}, ←set.union_assoc],
--       apply WEAK XBdC }
-- end

theorem provable.refl {A : Form} : {A} ⊢I A := ⟨by assump⟩

theorem provable.cut {X Y} (A : Form) {B} : X ∪ {A} ⊢I B → Y ⊢I A → X ∪ Y ⊢I B := sorry

lemma provable.premise_contraction {X A B} : X ∪ (X ∪ {A}) ⊢I B → X ∪ {A} ⊢I B := by obviously

instance provable.preorder (X : set Form): preorder Form :=
{ le := λ A B, X ∪ {A} ⊢I B,
  lt := λ A B, X ∪ {A} ⊢I B ∧ ¬ (X ∪ {B} ⊢I A),
  le_refl := λ A, ⟨by assump⟩,
  le_trans := λ A B C ApB BpC, provable.premise_contraction $ provable.cut B BpC ApB,
  lt_iff_le_not_le := λ A B, by refl }

def compactify {X A} : X ≻ A → {X' : finset Form // ↑X' ⊆ X ∧ ↑X' ⊢I A } :=
begin
intro dXA,
induction' dXA,
case weakening :
  { rcases ih with ⟨X', subX, X'pA⟩,
    use X',
    split, apply set.subset_union_of_subset_left,
    tidy },
case assumption :
  { use {A}, tidy,
    assump },
case and_intro : X A B dXA dXB ih₁ ih₂
  { rcases ih₁ with ⟨XA', AsubX, XA'pA⟩,
    rcases ih₂ with ⟨XB', BsubX, XB'pB⟩,
    constructor, swap, exact XA' ∪ XB',
    split, exact set.union_subset AsubX BsubX,
    split,
    exact set.finite.union finXA' finXB',
    rw proof_and_iff, split; apply @deduction.weakening _ _ (XA' ∪ XB'),
    constructor,
    apply ⋀I,
    apply WEAK _ dXA'A, apply set.subset_union_left,
    apply WEAK _ dXB'B, apply set.subset_union_right },
-- case and_left : 
--   { rcases ih with ⟨X', ⟨subX, X'pAB⟩⟩,
--     use X',
--     tidy,
--     apply ⋀E₁ A B, assumption },
-- case and_right : X A B
--   { rcases ih with ⟨X', ⟨subX, ⟨finX', pX'AB⟩⟩⟩,
--     cases pX'AB with dX'AB,
--     use X',
--     tidy,
--     apply ⋀E₂ A B, assumption },
-- case imp_intro : X A B
--   { rcases ih with ⟨X', ⟨subX, ⟨finX', pX'B⟩⟩⟩,
--     cases pX'B with dX'B,
--     use X' \ {A},
--     split,
--       rw set.diff_subset_iff, rw set.union_comm, assumption,
--     split,
--       apply set.finite.subset finX', obviously,
--     apply ⟹I,
--     apply WEAK _ dX'B,
--     apply set.subset_diff_union },
-- case imp_elim : X A B dXAB dA ihAB ihA
--   { rcases ihAB with ⟨X₁, ⟨sub₁X, ⟨finX₁, ⟨dX₁AB⟩⟩⟩⟩,
--     rcases ihA with ⟨X₂, ⟨sub₂X, ⟨finX₂, ⟨dX₂A⟩⟩⟩⟩,
--     use X₁ ∪ X₂,
--     split, exact set.union_subset sub₁X sub₂X,
--     split, exact set.finite.union finX₁ finX₂,
--     constructor,
--     apply ⟹E A,
--     apply WEAK _ dX₁AB, apply set.subset_union_left,
--     apply WEAK _ dX₂A, apply set.subset_union_right },
-- case or_left : X A B
--   { rcases ih with ⟨X', ⟨subX, ⟨finX', ⟨dX'A⟩⟩⟩⟩,
--     use X',
--     tidy,
--     exact ⋁I₁ A B dX'A
--     },
-- case or_right : X A B
--   { rcases ih with ⟨X', ⟨subX, ⟨finX', ⟨dX'B⟩⟩⟩⟩,
--     use X',
--     tidy,
--     exact ⋁I₂ A B dX'B
--     },
-- case or_elim : X A B C _ _ _ ih₁ ih₂ ih₃
--   {
--     rcases ih₁ with ⟨X₁, ⟨sub₁X, ⟨finX₁, ⟨dX₁AB⟩⟩⟩⟩,
--     rcases ih₂ with ⟨X₂, ⟨sub₂X, ⟨finX₂, ⟨dX₂C⟩⟩⟩⟩,
--     rcases ih₃ with ⟨X₃, ⟨sub₃X, ⟨finX₃, ⟨dX₃C⟩⟩⟩⟩,
--     use X₁ ∪ (X₂ \ {A}) ∪ (X₃ \ {B}),
--     split,
--       apply set.union_subset,
--         apply set.union_subset sub₁X, rw set.diff_subset_iff, rw set.union_comm, assumption,
--         rw set.diff_subset_iff, rw set.union_comm, assumption,
--     split,
--       apply @set.finite.subset _ (X₁ ∪ X₂ ∪ X₃),
--       apply set.finite.union,
--       apply set.finite.union,
--       assumption,
--       assumption,
--       assumption,
--       apply set.union_subset,
--       apply set.union_subset,
--       rw set.union_assoc,
--       apply set.subset_union_left,
--       rw set.diff_subset_iff,
--       apply set.subset_union_of_subset_right,
--       apply set.subset_union_of_subset_left,
--       apply set.subset_union_right,
--       rw set.diff_subset_iff,
--       apply set.subset_union_of_subset_right,
--       apply set.subset_union_right,
--       constructor,
--       apply ⋁E A B,
--       apply WEAK _ dX₁AB, rw set.union_assoc, apply set.subset_union_left,
--       apply WEAK _ dX₂C, 
--         rw set.union_assoc,
--         rw set.union_assoc,
--         apply set.subset_union_of_subset_right,
--         rw set.union_comm (X₃ \ {B}) {A},
--         rw ←set.union_assoc ,
--         apply set.subset_union_of_subset_left,
--         apply set.subset_diff_union,
--       apply WEAK _ dX₃C,
--         rw set.union_assoc,
--         rw set.union_assoc,
--         apply set.subset_union_of_subset_right,
--         apply set.subset_union_of_subset_right,
--         apply set.subset_diff_union
--    },
-- case falsum :
--   { rcases ih with ⟨X', ⟨subX, ⟨finX', ⟨dX'⟩⟩⟩⟩,
--     use X',
--     tidy,
--     exact ⊥E dX'
--   }
end

theorem compactness {X : set Form} {A : Form} : X ⊢I A → ∃ X' ⊆ X, X'.finite ∧ X' ⊢I A :=
begin
  intro pXA,
  cases pXA with dXA,
  induction' dXA,
  case weakening :
    { rcases ih with ⟨X', ⟨subX, ⟨finX',dX'A⟩⟩⟩,
      use X', split, apply set.subset_union_of_subset_left,
      tidy },
  case assumption :
    { use {A}, tidy,
      assump },
  case and_intro : X A B dXA dXB ih₁ ih₂
    { rcases ih₁ with ⟨XA', ⟨AsubX, ⟨finXA', pXA'A⟩⟩⟩,
      rcases ih₂ with ⟨XB', ⟨BsubX, ⟨finXB', pXB'B⟩⟩⟩,
      cases pXA'A with dXA'A,
      cases pXB'B with dXB'B,
      use XA' ∪ XB',
      split, exact set.union_subset AsubX BsubX,
      split,
      exact set.finite.union finXA' finXB',
      constructor,
      apply ⋀I,
      apply WEAK dXA'A,
      rw set.union_comm,
      apply WEAK dXB'B },
  case and_left : 
    { rcases ih with ⟨X', ⟨subX, ⟨finX', pX'AB⟩⟩⟩,
      cases pX'AB with dX'AB,
      use X',
      tidy,
      apply ⋀E₁ A B, assumption },
  case and_right : X A B
    { rcases ih with ⟨X', ⟨subX, ⟨finX', pX'AB⟩⟩⟩,
      cases pX'AB with dX'AB,
      use X',
      tidy,
      apply ⋀E₂ A B, assumption },
  case imp_intro : X A B
    { rcases ih with ⟨X', ⟨subX, ⟨finX', pX'B⟩⟩⟩,
      cases pX'B with dX'B,
      use X' \ {A},
      split,
        rw set.diff_subset_iff, rw set.union_comm, assumption,
      split,
        apply set.finite.subset finX', obviously,
      apply ⟹I,
      suffices : X' \ {A} ∪ {A} = X' ∪ {A}, rw this,
      apply WEAK dX'B,
      obviously },
  case imp_elim : X A B dXAB dA ihAB ihA
    { rcases ihAB with ⟨X₁, ⟨sub₁X, ⟨finX₁, ⟨dX₁AB⟩⟩⟩⟩,
      rcases ihA with ⟨X₂, ⟨sub₂X, ⟨finX₂, ⟨dX₂A⟩⟩⟩⟩,
      use X₁ ∪ X₂,
      split, exact set.union_subset sub₁X sub₂X,
      split, exact set.finite.union finX₁ finX₂,
      constructor,
      apply ⟹E A,
      apply WEAK dX₁AB,
      rw set.union_comm,
      apply WEAK dX₂A },
  case or_left : X A B
    { rcases ih with ⟨X', ⟨subX, ⟨finX', ⟨dX'A⟩⟩⟩⟩,
      use X',
      tidy,
      exact ⋁I₁ A B dX'A
      },
  case or_right : X A B
    { rcases ih with ⟨X', ⟨subX, ⟨finX', ⟨dX'B⟩⟩⟩⟩,
      use X',
      tidy,
      exact ⋁I₂ A B dX'B
      },
  case or_elim : X A B C _ _ _ ih₁ ih₂ ih₃
    {
      rcases ih₁ with ⟨X₁, ⟨sub₁X, ⟨finX₁, ⟨dX₁AB⟩⟩⟩⟩,
      rcases ih₂ with ⟨X₂, ⟨sub₂X, ⟨finX₂, ⟨dX₂C⟩⟩⟩⟩,
      rcases ih₃ with ⟨X₃, ⟨sub₃X, ⟨finX₃, ⟨dX₃C⟩⟩⟩⟩,
      use X₁ ∪ (X₂ \ {A}) ∪ (X₃ \ {B}),
      split,
        apply set.union_subset,
          apply set.union_subset sub₁X, rw set.diff_subset_iff, rw set.union_comm, assumption,
          rw set.diff_subset_iff, rw set.union_comm, assumption,
      split,
        apply @set.finite.subset _ (X₁ ∪ X₂ ∪ X₃),
        apply set.finite.union,
        apply set.finite.union,
        assumption,
        assumption,
        assumption,
        apply set.union_subset,
        apply set.union_subset,
        rw set.union_assoc,
        apply set.subset_union_left,
        rw set.diff_subset_iff,
        apply set.subset_union_of_subset_right,
        apply set.subset_union_of_subset_left,
        apply set.subset_union_right,
        rw set.diff_subset_iff,
        apply set.subset_union_of_subset_right,
        apply set.subset_union_right,
        constructor,
        apply ⋁E A B,
        rw set.union_assoc,
        apply WEAK dX₁AB,
        rw set.union_assoc,
        rw set.union_assoc,
        apply set.subset_union_of_subset_right,
        rw set.union_comm (X₃ \ {B}) {A},
        rw ←set.union_assoc,
        apply set.subset_diff_union,
        apply WEAK dX₂C, 
          apply set.subset_union_of_subset_left,
        apply WEAK _ dX₃C,
          rw set.union_assoc,
          rw set.union_assoc,
          apply set.subset_union_of_subset_right,
          apply set.subset_union_of_subset_right,
          apply set.subset_diff_union
     },
  case falsum :
    { rcases ih with ⟨X', ⟨subX, ⟨finX', ⟨dX'⟩⟩⟩⟩,
      use X',
      tidy,
      exact ⊥E dX'
    }
end

end nat_deduction
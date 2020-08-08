/-
Chapter 6: Soundness and Completeness
Author: Billy Price
-/
import definitions chapter5

namespace nat_deduction

def soundness {X : set Form} {A : Form} : X ⊢I A → X ⊨ A :=
begin
  rintro ⟨XdA⟩,
  induction' XdA,
  case weakening {exact boolean.valid_weakening ih},
  case assumption {tauto},
  case and_intro {apply boolean.and_iff.mpr, tidy },
  case and_left {rw boolean.and_iff at *, tidy },
  case and_right {rw boolean.and_iff at *, tidy },
  case imp_intro {apply boolean.imp_iff.mpr, tidy},
  case imp_elim {rw boolean.imp_iff at *, rw ←set.union_self X, apply boolean.valid_cut A, tidy },
  case or_left { intros M hM, simp, exact or.inl (ih _ hM) },
  case or_right { intros M hM, simp, exact or.inr (ih _ hM) },
  case or_elim : X A B C _ _ _ ihAB ihA ihB 
    { intros M hM,
      specialize ihAB M hM, simp * at *,
      cases ihAB, 
        apply ihA, simp, tidy,
        apply ihB, simp, tidy, },
  case falsum { intros M hM, specialize ih M hM, contradiction }
end

namespace intuitionistic

def maximal_avoiding (A : Form) : Type := { X : set Form // ¬(X ⊢I A) ∧ ∀ B ∉ X, X ∪ {B} ⊢I A}

namespace maximal

variables {X Y : set Form}
variables {A B C : Form}

open classical
local attribute [instance] prop_decidable

lemma mem_of_provable (X : maximal_avoiding A) : X.1 ⊢I B → B ∈ X.1 :=
begin
  rcases X with ⟨X,nXdA,hX⟩,
  rintro XpB, simp at *,
  by_contradiction h,
  apply nXdA,
  rw ←set.union_self X,
  apply provable.cut B _ XpB,
  exact hX _ h
end

lemma bot_not_mem (X : maximal_avoiding A) : (⊥ : Form) ∉ X.1 :=
begin
  intro bmem,
  apply X.2.1,
  apply provable.explosion,
  constructor, assump,
end

lemma and_mem_iff (X : maximal_avoiding A) : B ⋀ C ∈ X.1 ↔ B ∈ X.1 ∧ C ∈ X.1 :=
begin
  rcases X with ⟨X,XnA,hX⟩,
  split,
    intro mBC, split; apply mem_of_provable; simp * at *,
    constructor, apply ⋀E₁ B C, assump,
    constructor, apply ⋀E₂ B C, assump,
  rintros ⟨mB, mC⟩,
  apply mem_of_provable, simp,
  constructor, apply ⋀I; assump
end

lemma or_mem_iff (X : maximal_avoiding A) : B ⋁ C ∈ X.1 ↔ B ∈ X.1 ∨ C ∈ X.1 :=
begin
  split,
    intro mBC,
    by_contradiction h,
    rw not_or_distrib at h,
    rcases X with ⟨X, nXpA, hX⟩,
    rcases hX B h.1 with hB,
    rcases hX C h.2 with hC,
    apply nXpA, constructor,
    apply ⋁E B C, assump, assumption, assumption,
  rintro (mB | mC); apply mem_of_provable; constructor,
  apply ⋁I₁, assump,
  apply ⋁I₂, assump
end

lemma or_of_imp_mem (X : maximal_avoiding A) : B ⟹ C ∈ X.1 → B ∉ X.1 ∨ C ∈ X.1 :=
begin
  intro mBC,
  by_cases B ∈ X.val,
  apply or.inr,
  apply mem_of_provable,
  constructor,
  apply ⟹E B; assump,
  exact or.inl h
end

lemma nmem_of_neg_mem (X : maximal_avoiding A) : (¬ B) ∈ X.1 → B ∉ X.1 :=
begin
  intro nbmem,
  cases or_of_imp_mem X nbmem, assumption,
  apply absurd h,
  exact bot_not_mem _
end


end maximal

end intuitionistic

/-TODO: Lemma 5. If X is a maximal A-avoiding set in a logic L that at least
contains all of the rules of classical logic, then X also satisfies the
following conditions:
  * ¬B ∈ X iff. B ∉ X
  * B ⟹ C ∈ X iff. B ∉ X or C ∈ X

(Will require classical logic provability)
-/

/-TODO: Lemma 6. If X is a maximal A-avoiding set in a logic L that
contains all of the rules of classical logic, then there is some valuation v_X
where for any formula B,
 * v_X(B) iff. B ∈ X
-/

/-TODO: Lemma 7. For any logic L, if X ⊬L A then there is some maximal A-excluding
set Y where Y ⊆ X -/

/-TODO: Completeness of Classical Logic-/

section heyting_algebra

universe u

class heyting_alegebra (α : Type u) extends bounded_lattice α :=
(imp : α → α → α)
(imp_prop : ∀ x y z : α, x ⊓ y ≤ z ↔ x ≤ imp y z)

-- Define valuation on a heyting algebra

end heyting_algebra


/-TODO: Chapter 6 Exercises-/


end nat_deduction
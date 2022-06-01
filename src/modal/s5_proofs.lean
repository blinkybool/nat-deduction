import modal.S5
import tactic
-- set_option trace.class_instances true

variable {α : Type}

example {A : MForm α} : {¬◇A} ≻₅ (□¬A) :=
begin
  apply □I {¬◇A},
  rw modal_singleton,
  exact modal.mk_neg_pos,
  tidy,
  apply ¬I,
  apply ¬E' ◇A, assump,
  apply ◇I, assump
end

example {p q : α} : {◇(□↑p ⋀ ¬(↑q)), ◇(□q ⋀ ¬p)} ≻₅ ⊥ :=
begin
  apply ◇E {◇(□q ⋀ ¬p)} (□p ⋀ ¬q),
  simp, exact modal.mk_pos, assump,
  apply ¬E □p,
  apply ¬I,
  apply ◇E _ (□q ⋀ ¬p), simp, exact modal.mk_nec, assump,
  rw set.union_comm,
  apply ¬E p,
  apply ⋀E₂, assump,
  apply □E, assump,
  apply ⋀E₁, assump
end

def chain {X Y : set MForm} {A B : MForm} : X ≻₅ A → Y ∪ {A} ≻₅ B → X ∪ Y ≻₅ B :=
begin
  intros XdA YAdC,
  rw set.union_comm,
  exact ⟹E A (⟹I YAdC) XdA
end

def deMorgan₁ (A B : MForm) : {¬(A ⋀ B)} ≻₅ (¬A) ⋁ (¬B) :=
begin
  apply DNE,
  apply ¬I, simp,
  apply ¬E' (A ⋀ B), assump,
  apply ⋀I';
  apply DNE;
  apply ¬I;
  apply ¬E' ((¬A) ⋁ (¬B)),
  assump,
  apply ⋁I₁, assump,  
  assump,
  apply ⋁I₂, assump
end

def or_cons (A B) {A' B'} : {A} ≻₅ A' → {B} ≻₅ B' → ∅ ≻₅ A ⋁ B → ∅ ≻₅ A' ⋁ B' :=
begin
  intros AdA' BdB' dAB,
  convert @chain ∅ ∅ (A ⋁ B) _ _ _, tidy, exact dAB,
  convert @S5.deduction.or_elim {A ⋁ B} ∅ ∅ A B _ _ _ _, simp,
  assump,
  simp, apply ⋁I₁ AdA',
  simp, apply ⋁I₂ BdB',
end

lemma deMorgan_pos (A) : {¬◇A} ≻₅ □¬A :=
begin
  apply □I', simp, exact modal.mk_neg_pos,
  apply ¬I,
  apply ¬E ◇A, assump,
  apply ◇I, assump
end

lemma deMorgan_imp_inv {A B} : {¬(A ⋀ ¬B)} ≻₅ A ⟹ B  :=
begin
  apply ⟹I,
  apply DNE,
  apply ¬I,
  rw set.union_assoc,
  apply ¬E (A ⋀ ¬B), assump,
  apply ⋀I; assump,
end

example {p q : ℕ} : ∅ ≻₅ (□((□p) ⟹ q) ⋁ □((□q) ⟹ p))  :=
begin
  apply or_cons (¬◇((□p) ⋀ ¬q)) (¬◇((□q) ⋀ ¬p)),
  

end

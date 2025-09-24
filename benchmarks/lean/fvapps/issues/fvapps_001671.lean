-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mkFamily : Family := {
  male := fun _ => false,
  female := fun _ => false,
  get_parents_of := fun _ => [],
  get_children_of := fun _ => [],
  set_parent_of := fun _ _ => false,
  is_male := fun _ => false,
  is_female := fun _ => false
}

variable (f : Family)
-- </vc-definitions>

-- <vc-theorems>
theorem male_female_exclusive (name : String) :
  ¬(f.male name = true ∧ f.female name = true) :=
sorry

theorem male_idempotent (name : String) :
  f.male name = true → f.male name = true ∧ f.female name = false :=
sorry

theorem female_idempotent (name : String) :
  f.female name = true → f.female name = true ∧ f.male name = false :=
sorry

theorem empty_relationships (name : String) :
  f.get_parents_of name = [] ∧ 
  f.get_children_of name = [] ∧
  f.is_male name = false ∧
  f.is_female name = false :=
sorry

theorem parent_child_relationship (parent child : String) :
  parent ≠ child →
  (f.set_parent_of child parent = true → 
    (parent ∈ f.get_parents_of child ∧
     child ∈ f.get_children_of parent ∧
     (f.get_parents_of child).length ≤ 2)) ∧
  (f.set_parent_of child parent = false →
    parent ∉ f.get_parents_of child ∧
    child ∉ f.get_children_of parent) :=
sorry

theorem gender_deduction (parent1 parent2 child : String) :
  parent1 ≠ parent2 ∧ parent1 ≠ child ∧ parent2 ≠ child →
  f.set_parent_of child parent1 = true ∧ f.set_parent_of child parent2 = true →
  f.male parent1 = true →
  f.is_female parent2 = true ∧
  f.is_male parent1 ≠ f.is_male parent2 ∧ 
  f.is_female parent1 ≠ f.is_female parent2 :=
sorry

theorem no_cyclic_relationships (names : List String) :
  names.length ≥ 3 →
  names.Nodup →
  (∀ (i : Nat), i < names.length - 1 → 
    f.set_parent_of (names[i]!) (names[i+1]!) = true) →
  f.set_parent_of (names[names.length - 1]!) (names[0]!) = false :=
sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flatten_me {α : Type u} (lst : List (List α ⊕ α)) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flatten_no_nesting {α : Type u} :
  ∀ (lst : List α), flatten_me (lst.map fun x => Sum.inr x) = lst :=
  sorry

theorem flatten_properties {α : Type u} (lst : List (List α ⊕ α)) :
  let flattened := flatten_me lst
  let atomic_elements := lst.filterMap (fun x => match x with
                                               | Sum.inl _ => none
                                               | Sum.inr a => some a)
  let nested_elements := lst.filterMap (fun x => match x with 
                                               | Sum.inl l => some l
                                               | Sum.inr _ => none)
  let nested_lengths := lst.filterMap (fun x => match x with 
                                              | Sum.inl l => some l.length
                                              | Sum.inr _ => none)
  -- Property 1: All elements in output are atomic (implicitly handled by return type)
  -- Property 2: All original elements are preserved (through list membership)
  (∀ x, x ∈ atomic_elements → x ∈ flattened) ∧
  (∀ l x, l ∈ nested_elements → x ∈ l → x ∈ flattened) ∧
  (∀ x, x ∈ flattened → x ∈ atomic_elements ∨ ∃ l, l ∈ nested_elements ∧ x ∈ l) ∧
  -- Property 3: Length is sum of atomic elements and nested lengths
  flattened.length = atomic_elements.length + nested_lengths.foldl (·+·) 0 :=
  sorry
-- </vc-theorems>
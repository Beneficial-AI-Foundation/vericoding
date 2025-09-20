-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def normalize {α : Type} (lst : List (List α ⊕ α)) : List (List α ⊕ α) := sorry

theorem normalize_identity_flat {α : Type} (lst : List α) :
  normalize (lst.map (fun x => Sum.inr x)) = lst.map (fun x => Sum.inr x) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem normalize_sublist_lengths {α : Type} (lst : List (List α ⊕ α)) :
  (∃ x y, x ∈ lst ∧ y ∈ lst ∧ ∃ l1 l2, x = Sum.inl l1 ∧ y = Sum.inl l2) →
  (∀ x y, x ∈ normalize lst → y ∈ normalize lst → 
    match x, y with 
    | Sum.inl l1, Sum.inl l2 => List.length l1 = List.length l2
    | _, _ => True) := sorry

theorem normalize_empty {α : Type} :
  normalize ([] : List (List α ⊕ α)) = [] := sorry

theorem normalize_singleton_empty {α : Type} :
  normalize [Sum.inl ([] : List α)] = [Sum.inl []] := sorry
-- </vc-theorems>
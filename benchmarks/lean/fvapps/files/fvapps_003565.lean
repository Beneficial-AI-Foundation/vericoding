-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sortme (words : List String) : List String := sorry

def multiset_eq (l1 l2 : List String) : Prop :=
  ∀ x, (List.countP (· = x) l1) = (List.countP (· = x) l2)
-- </vc-definitions>

-- <vc-theorems>
theorem sortme_maintains_length (words : List String) : 
  List.length (sortme words) = List.length words ∧ 
  multiset_eq (sortme words) words := sorry

theorem sortme_ordered_case_insensitive (words : List String) :
  ∀ i, i < (sortme words).length - 1 →
  String.toLower ((sortme words)[i]!) ≤ String.toLower ((sortme words)[i+1]!) := sorry

theorem sortme_stable_for_equal_items (words : List String) :
  ∀ i, i < (sortme words).length - 1 → 
  String.toLower ((sortme words)[i]!) = String.toLower ((sortme words)[i+1]!) →
  ((sortme words)[i]!) ≤ ((sortme words)[i+1]!) := sorry

theorem sortme_empty_list :
  sortme [] = [] := sorry

theorem sortme_idempotent (words : List String) :
  sortme (sortme words) = sortme words := sorry
-- </vc-theorems>
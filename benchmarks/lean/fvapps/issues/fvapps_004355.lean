-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def combine {α : Type u} (lists : List (List α)) : List α := sorry

theorem combine_preserves_elements {α : Type u} (lists : List (List α)) (h : lists ≠ []) :
  ∀ (lst : List α), lst ∈ lists → ∀ (x : α), x ∈ lst → x ∈ combine lists := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem combine_length {α : Type u} (lists : List (List α)) (h : lists ≠ []) :
  let maxLen := (lists.map List.length).maximum?.getD 0
  let minLen := (lists.map (fun l => min l.length maxLen)).foldl (· + ·) 0
  List.length (combine lists) = minLen := sorry

theorem combine_interleaving {α : Type u} (lists : List (List α)) 
  (h1 : lists ≠ []) (h2 : lists.length ≥ 2)
  (i j : Nat) (hi : i < (lists.map List.length).minimum?.getD 0) (hj : j < lists.length) :
  let minLen := (lists.map List.length).minimum?.getD 0
  (combine lists).get? (i * lists.length + j) = (lists.get? j).bind (fun l => l.get? i) := sorry
-- </vc-theorems>
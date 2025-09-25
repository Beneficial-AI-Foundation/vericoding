-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Skiplist.new : Skiplist := sorry

def List.toFinset (l : List Nat) : List Nat := 
  match l with
  | [] => []
  | h :: t => if h ∈ t then List.toFinset t else h :: List.toFinset t
-- </vc-definitions>

-- <vc-theorems>
theorem add_search_property (l : List Nat) (h : ∀ x ∈ l, x ≤ 20000) :
  let sl := Skiplist.new 
  ∀ x ∈ l.toFinset,
    (List.foldl (λ acc n => let _ := acc.add n; acc) sl l).search x := sorry

theorem search_missing_property (l : List Nat) (n : Nat) 
    (h₁ : ∀ x ∈ l, x ≤ 20000)
    (h₂ : n > 20000 ∨ n < 0) :
  let sl := Skiplist.new
  ¬((List.foldl (λ acc x => let _ := acc.add x; acc) sl l).search n) := sorry

theorem erase_property (l : List Nat) (h : ∀ x ∈ l, x ≤ 20000) :
  let sl := Skiplist.new
  let sl' := List.foldl (λ acc x => let _ := acc.add x; acc) sl l
  ∀ x ∈ l.toFinset,
    (∀ i < l.count x, sl'.erase x) ∧
    (¬sl'.erase x) ∧
    (¬sl'.search x) := sorry

theorem duplicate_property (n : Nat) (r : Nat)
    (h₁ : n ≤ 20000) 
    (h₂ : 0 < r ∧ r ≤ 100) :
  let sl := Skiplist.new
  let sl' := List.foldl (λ acc _ => let _ := acc.add n; acc) sl (List.replicate r ())
  (∀ i < r, sl'.erase n) ∧ 
  (¬sl'.search n) ∧
  (¬sl'.erase n) := sorry
-- </vc-theorems>
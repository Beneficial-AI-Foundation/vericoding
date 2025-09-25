-- <vc-preamble>
def get_area (x : AreaElement) : Nat :=
  match x with
  | .circle r => 314159 * r * r / 100000  -- π approximation times r^2
  | .rect (w, h) => w * h
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_by_area (seq : List AreaElement) : List AreaElement :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_by_area_preserves_length {seq : List AreaElement} :
  (sort_by_area seq).length = seq.length :=
  sorry

theorem sort_by_area_preserves_elements {seq : List AreaElement} (x : AreaElement) :
  (seq.count x) = ((sort_by_area seq).count x) :=
  sorry

theorem sort_by_area_ascending {seq : List AreaElement} :
  ∀ i j, i < j → j < (sort_by_area seq).length →
    let sorted := sort_by_area seq
    ∀ (hi : i < sorted.length) (hj : j < sorted.length),
    get_area (sorted.get ⟨i, hi⟩) ≤ get_area (sorted.get ⟨j, hj⟩) :=
  sorry

theorem sort_by_area_empty :
  sort_by_area [] = [] :=
  sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval sort_by_area []

/-
info: expected
-/
-- #guard_msgs in
-- #eval sort_by_area [(4.23, 6.43), 1.23, 3.444, (1.342, 3.212)]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval sort_by_area [1.0, 2.0, 3.0]
-- </vc-theorems>
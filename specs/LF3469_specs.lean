-- <vc-preamble>
def Rat.add (a b : Rat) : Rat := sorry
def Rat.sub (a b : Rat) : Rat := sorry

def Rat.le (a b : Rat) : Prop := sorry
def Rat.abs (a : Rat) : Rat := sorry

def Int.toRat (n : Int) : Rat := sorry
def Nat.toRat (n : Nat) : Rat := sorry

def Float.toRat (f : Float) : Rat := sorry

instance : Add Rat where
  add := Rat.add

instance : Sub Rat where
  sub := Rat.sub

instance : LE Rat where
  le := Rat.le
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decompose (f : Rat) : List Rat := sorry

/- The sum of decomposed unit fractions equals the input rational number -/
-- </vc-definitions>

-- <vc-theorems>
theorem decompose_sum_equals_input (f : Rat) (h : Rat.le ⟨0, 1, by simp⟩ f) (h2 : Rat.le f ⟨10, 1, by simp⟩) :
  let parts := decompose f
  let sum_parts := parts.foldl Rat.add ⟨0, 1, by simp⟩
  Rat.le (Rat.abs (Rat.sub sum_parts f)) ⟨1, 100000, by simp⟩ := sorry

/- For non-whole numbers, decomposition yields unique descending unit fractions -/

theorem decompose_unique_unit_fractions (f : Rat) (h : Rat.le ⟨0, 1, by simp⟩ f) (h2 : Rat.le f ⟨10, 1, by simp⟩) :
  let parts := decompose f
  (parts.length > 1) →
  let unit_fracs := parts.tail
  (∀ x ∈ unit_fracs, ∃ (n : Nat) (h : n > 0), x = ⟨1, n, h⟩) ∧ 
  List.Pairwise (fun x y => Rat.le y x) unit_fracs ∧
  List.Nodup unit_fracs := sorry

/- Decomposition of whole numbers returns singleton list -/

theorem decompose_whole_numbers (n : Nat) (h : n > 0) (h2 : n ≤ 100) :
  decompose (Nat.toRat n) = [Nat.toRat n] := sorry

/- Decimal inputs are handled properly -/

theorem decompose_decimals (d : Float) (h : d ≥ 0) (h2 : d ≤ 10) :
  let result := decompose (Float.toRat d)
  let sum_parts := result.foldl Rat.add ⟨0, 1, by simp⟩
  Rat.le (Rat.abs (Rat.sub sum_parts (Float.toRat d))) ⟨1, 100000, by simp⟩ := sorry

/-
info: ['1/2', '1/4']
-/
-- #guard_msgs in
-- #eval decompose "3/4"

/-
info: ['1/2', '1/7', '1/59', '1/5163', '1/53307975']
-/
-- #guard_msgs in
-- #eval decompose "0.66"

/-
info: ['1/2', '1/4', '1/20']
-/
-- #guard_msgs in
-- #eval decompose "4/5"
-- </vc-theorems>
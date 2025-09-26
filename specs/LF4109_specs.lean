-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def skiponacci (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem skiponacci_output_type (n : Nat) (h : n > 0) : 
  (String.splitOn (skiponacci n) " ").length > 0 := sorry

theorem skiponacci_length (n : Nat) (h : n > 0) :
  (String.splitOn (skiponacci n) " ").length = n := sorry

theorem skiponacci_odd_indices_skip (n : Nat) (h : n > 0) :
  ∀ i : Nat, i < n → i % 2 = 1 → 
    ((String.splitOn (skiponacci n) " ")[i]'sorry) = "skip" := sorry

theorem skiponacci_first_element (n : Nat) (h : n > 0) :  
  (String.splitOn (skiponacci n) " ").head? = some "1" := sorry

theorem skiponacci_even_indices_increasing (n : Nat) (h : n > 0) :
  let evenNumbers := (String.splitOn (skiponacci n) " ").enum.filter (fun p => p.fst % 2 = 0)
  ∀ i j : Nat, i < j → j < evenNumbers.length →
    String.toNat! (evenNumbers[i]'sorry).snd < String.toNat! (evenNumbers[j]'sorry).snd := sorry

/-
info: '1'
-/
-- #guard_msgs in
-- #eval skiponacci 1

/-
info: '1 skip 2 skip 5'
-/
-- #guard_msgs in
-- #eval skiponacci 5

/-
info: '1 skip 2 skip 5 skip 13'
-/
-- #guard_msgs in
-- #eval skiponacci 7
-- </vc-theorems>
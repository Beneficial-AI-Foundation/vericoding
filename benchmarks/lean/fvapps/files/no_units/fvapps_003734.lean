-- <vc-preamble>
def pattern (n : Nat) : String := sorry

theorem pattern_non_positive (n : Nat) (h : n = 0) : 
  pattern n = "" := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_lines (n : Nat) : List String :=
  (pattern n).split (· = '\n')
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_first_line (n : Nat) (h : n > 0) :
  (get_lines n)[0]! = String.join (List.map toString (List.range n)) := sorry 

theorem pattern_line_count (n : Nat) (h : n > 0) :
  (get_lines n).length = n := sorry

theorem pattern_line_length (n : Nat) (h : n > 0) (i : Nat) (h2 : i < n) :
  (get_lines n)[i]!.length = n - i := sorry

theorem pattern_line_starts_with_n (n : Nat) (h : n > 0) (i : Nat) (h2 : i < n) :
  (get_lines n)[i]!.front.toString = toString n := sorry

theorem pattern_descending_numbers (n : Nat) (h : n > 0) (i : Nat) (h2 : i < n) :
  let nums := (get_lines n)[i]!.data.map (λ c => c.toString.toNat!);
  nums == (List.range (n - i)).map (λ x => n - x) := sorry
-- </vc-theorems>
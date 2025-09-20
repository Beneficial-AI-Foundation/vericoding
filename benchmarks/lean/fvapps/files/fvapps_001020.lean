-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generatePattern (k : Nat) : List String := sorry

theorem generate_pattern_length {k : Nat} :
  List.length (generatePattern k) = k + 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem generate_pattern_first_element {k : Nat} :
  List.head! (generatePattern k) = "0" := sorry

theorem generate_pattern_stars_count {k : Nat} {i : Nat} (h : i > 0) (h2 : i ≤ k) :
  let row := (generatePattern k).get! i
  let count := row.foldl (fun acc c => if c = '*' then acc + 1 else acc) 0
  count = i := sorry

theorem generate_pattern_row_format {k : Nat} {i : Nat} (h : i > 0) (h2 : i ≤ k) :
  let row := (generatePattern k).get! i
  row = String.mk (List.replicate i '*') ++ toString i := sorry

theorem generate_pattern_empty :
  generatePattern 0 = ["0"] := sorry
-- </vc-theorems>
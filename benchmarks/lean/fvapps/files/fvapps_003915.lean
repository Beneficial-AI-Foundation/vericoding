-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bears (n : Nat) (s : String) : String × Bool := sorry

theorem bears_return_structure (n : Nat) (s : String) :
  let res := bears n s
  res.1.data.all (fun c => c = 'B' ∨ c = '8') ∧ 
  res.1.length % 2 = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bears_output_length_determines_bool (n : Nat) (s : String) : 
  let res := bears n s
  res.2 = (res.1.length / 2 ≥ n) := sorry

theorem bears_output_is_subset (n : Nat) (s : String) :
  let res := bears n s
  let filtered := s.data.filter (fun c => c = 'B' ∨ c = '8')
  res.1.data.all (fun pair => filtered.contains pair) := sorry

theorem bears_captures_all_pairs (n : Nat) (s : String) 
  (h : s.data.all (fun c => c = 'B' ∨ c = '8')) :
  let res := bears n s
  let numPairs := res.1.length / 2
  let countValidPairs := (s.data.zip (s.data.drop 1))
    |>.filter (fun p => (p.1 = 'B' ∧ p.2 = '8') ∨ 
                       (p.1 = '8' ∧ p.2 = 'B'))
    |>.length
  numPairs = countValidPairs := sorry
-- </vc-theorems>
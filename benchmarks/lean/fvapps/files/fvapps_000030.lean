-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_string_alternation (n : Nat) (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_string_alternation_properties (s : String) (n : Nat)
  (h1 : s.length = n) (h2 : n > 0) (h3 : ∀c ∈ s.data, c = '0' ∨ c = '1') :
  let result := solve_string_alternation n s
  let adjacent_same := (List.zip s.data s.data.tail).filter (fun p => p.1 = p.2) |>.length
  (result ≥ 0) ∧
  (result < n) ∧
  (result = (adjacent_same + adjacent_same % 2) / 2) :=
sorry

theorem solve_string_alternation_perfect_alt (n : Nat) (h : n ≥ 2) :
  let s := String.mk (List.map (fun i => if i % 2 = 0 then '0' else '1') (List.range n))
  solve_string_alternation n s = 0 :=
sorry

theorem solve_string_alternation_all_same (n : Nat) (h : n > 0) :
  let s := String.mk (List.replicate n '0')
  solve_string_alternation n s = ((n-1) + (n-1) % 2) / 2 :=
sorry
-- </vc-theorems>
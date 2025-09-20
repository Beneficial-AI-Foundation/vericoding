-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minTaps (n: Nat) (ranges: List Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_ranges_theorem (n: Nat) (h: n ≥ 1) (h2: n ≤ 100):
  minTaps n (List.replicate (n+1) 0) = -1 := sorry

theorem full_coverage_theorem (n: Nat) (h: n ≥ 1) (h2: n ≤ 100):
  let ranges := (List.replicate (n+1) 0).set 0 n
  minTaps n ranges = 1 := sorry 

theorem alternating_ranges_theorem (n: Nat) (h: n ≥ 1) (h2: n ≤ 100):
  let ranges := List.range (n+1) |>.map (fun i => if i % 2 = 0 then 1 else 0)
  minTaps n ranges = -1 ∨ minTaps n ranges ≥ n/2 := sorry

theorem basic_properties_theorem (n: Nat) (ranges: List Nat) 
  (h: n ≥ 1) (h2: n ≤ 100) (h3: ranges.length = n+1):
  minTaps n ranges = -1 ∨ minTaps n ranges ≥ 1 := sorry

theorem all_zeros_theorem (n: Nat) (ranges: List Nat)
  (h: n ≥ 1) (h2: n ≤ 100) (h3: ranges.length = n+1)
  (h4: ranges.all (fun x => x = 0)):
  minTaps n ranges = -1 := sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def determine_server (p1 : Nat) (p2 : Nat) (k : Nat) : String :=
  sorry

-- Only two possible results
-- </vc-definitions>

-- <vc-theorems>
theorem determine_server_two_values (p1 p2 k : Nat) (h : k > 0) :
  determine_server p1 p2 k = "CHEF" ∨ determine_server p1 p2 k = "COOK" :=
  sorry

-- Result only depends on total modulo 2k

theorem determine_server_cycle (p1 p2 k : Nat) (h : k > 0) :
  determine_server (p1 + p2 + 2*k) 0 k = determine_server p1 p2 k :=
  sorry

-- CHEF serves first k points in cycle

theorem determine_server_chef (p1 p2 k : Nat) (h : k > 0) :
  (p1 + p2) % (2*k) < k → determine_server p1 p2 k = "CHEF" :=
  sorry

-- COOK serves second k points in cycle  

theorem determine_server_cook (p1 p2 k : Nat) (h : k > 0) :
  (p1 + p2) % (2*k) ≥ k → determine_server p1 p2 k = "COOK" :=
  sorry

-- Result is independent of point distribution

theorem determine_server_point_split (total k : Nat) (h : k > 0) :
  determine_server total 0 k = determine_server 0 total k :=
  sorry

theorem determine_server_point_split_one (total k : Nat) (h : k > 0) (h2 : total > 0) :
  determine_server total 0 k = determine_server (total-1) 1 k :=
  sorry
-- </vc-theorems>
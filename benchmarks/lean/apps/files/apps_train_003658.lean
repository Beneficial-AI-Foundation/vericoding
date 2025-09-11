-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ipsBetween (start_ip end_ip : String) : Int := sorry

theorem ipsBetween_range (start_ip end_ip : String) :
  let result := ipsBetween start_ip end_ip
  result ≥ 0 ∧ result < 2^32 := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ipsBetween_self (ip : String) :
  ipsBetween ip ip = 0 := by sorry

theorem ipsBetween_symmetry 
  (ip1 ip2 : String)
  (h : ipsBetween ip1 ip2 > 0) : 
  ipsBetween ip2 ip1 = -(ipsBetween ip1 ip2) := by sorry

/-
info: 50
-/
-- #guard_msgs in
-- #eval ips_between "10.0.0.0" "10.0.0.50"

/-
info: 246
-/
-- #guard_msgs in
-- #eval ips_between "20.0.0.10" "20.0.1.0"

/-
info: 256
-/
-- #guard_msgs in
-- #eval ips_between "160.0.0.0" "160.0.1.0"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded
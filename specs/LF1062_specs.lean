-- <vc-preamble>
def find_min_contest_time (n x y : Nat) (contests : List (Nat × Nat)) 
    (v_times w_times : List Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxsize : Nat := 4294967295 -- Using max u32 as stand-in for sys.maxsize

theorem find_min_contest_time_positive
    (n x y : Nat)
    (contests : List (Nat × Nat))
    (v_times w_times : List Nat)
    (h1 : n > 0)
    (h2 : x > 0)
    (h3 : y > 0)
    (h4 : contests.length > 0)
    (h5 : v_times.length > 0)
    (h6 : w_times.length > 0)
    (h7 : ∀ c ∈ contests, c.1 ≥ 0 ∧ c.2 ≤ 100 ∧ c.1 < c.2)
    (h8 : ∀ t ∈ v_times, t ≤ 100)
    (h9 : ∀ t ∈ w_times, t ≤ 100) :
    find_min_contest_time n x y contests v_times w_times > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_contest_time_exceeds_min_duration
    (n x y : Nat)
    (contests : List (Nat × Nat))
    (v_times w_times : List Nat)
    (h1 : n > 0)
    (h2 : x > 0)
    (h3 : y > 0)
    (h4 : contests.length > 0)
    (h5 : v_times.length > 0)
    (h6 : w_times.length > 0)
    (h7 : ∀ c ∈ contests, c.1 ≥ 0 ∧ c.2 ≤ 100 ∧ c.1 < c.2) 
    (h8 : ∀ t ∈ v_times, t ≤ 100)
    (h9 : ∀ t ∈ w_times, t ≤ 100)
    (result := find_min_contest_time n x y contests v_times w_times)
    (min_duration := (contests.map (fun c => c.2 - c.1)).minimum?) :
    result ≠ maxsize → result ≥ min_duration.getD 0 := sorry

theorem find_min_contest_time_order_invariant
    (contests : List (Nat × Nat))
    (v_times w_times : List Nat) 
    (h1 : contests.length > 0)
    (h2 : v_times.length > 0)
    (h3 : w_times.length > 0)
    (h4 : ∀ c ∈ contests, c.1 ≥ 0 ∧ c.2 ≤ 100 ∧ c.1 < c.2)
    (h5 : ∀ t ∈ v_times, t ≤ 100)
    (h6 : ∀ t ∈ w_times, t ≤ 100)
    (sorted_v := v_times)
    (sorted_w := w_times) :
    find_min_contest_time 1 1 1 contests v_times w_times = 
    find_min_contest_time 1 1 1 contests sorted_v sorted_w := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval find_min_contest_time 3 4 2 [(15, 21), (5, 10), (7, 25)] [4, 14, 25, 2] [13, 21]
-- </vc-theorems>
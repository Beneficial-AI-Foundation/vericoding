-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def canIPlay (now start finish : Nat) : Bool := sorry

theorem canIPlay_symmetry_24 (now start finish : Nat) :
  canIPlay now start finish = canIPlay (now + 24) start finish := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem canIPlay_symmetry_start_finish (now start finish : Nat) :
  canIPlay now start finish = canIPlay now (start + 24) (finish + 24) := sorry

theorem canIPlay_relative_times (now start finish : Nat) :
  canIPlay now start finish = 
  canIPlay (now - start) 0 ((finish - start) % 24) := sorry

theorem canIPlay_same_start_finish (now start : Nat) :
  ¬(canIPlay now start start) := sorry

theorem canIPlay_window_contains_start 
  (start window : Nat) (h : 0 < window) (h2 : window < 24) :
  canIPlay start start ((start + window) % 24) := sorry
-- </vc-theorems>
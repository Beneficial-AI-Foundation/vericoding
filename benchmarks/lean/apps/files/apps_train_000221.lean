-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def push_dominoes (s : String) : String := sorry

theorem length_preserved (s : String) :
  s.all (fun c => c = '.' ∨ c = 'L' ∨ c = 'R') →
  (push_dominoes s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_chars_preserved (s : String) :
  s.all (fun c => c = '.' ∨ c = 'L' ∨ c = 'R') →
  (push_dominoes s).all (fun c => c = '.' ∨ c = 'L' ∨ c = 'R') := sorry

theorem idempotent (s : String) :
  s.all (fun c => c = '.' ∨ c = 'L' ∨ c = 'R') →
  push_dominoes (push_dominoes s) = push_dominoes s := sorry

theorem no_dots_unchanged (s : String) :
  s.all (fun c => c = 'L' ∨ c = 'R') →
  push_dominoes s = s := sorry

theorem all_dots_stay_dots (s : String) :
  s.all (fun c => c = '.') →
  (push_dominoes s).all (fun c => c = '.') := sorry

/-
info: 'LL.RR.LLRRLL..'
-/
-- #guard_msgs in
-- #eval push_dominoes ".L.R...LR..L.."

/-
info: 'RR.L'
-/
-- #guard_msgs in
-- #eval push_dominoes "RR.L"

/-
info: '...'
-/
-- #guard_msgs in
-- #eval push_dominoes "..."
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded
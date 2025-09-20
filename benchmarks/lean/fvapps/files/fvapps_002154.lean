-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_thor_notifications (n: Nat) (events: List (Nat × Nat)) : List Nat := sorry

theorem only_generate_notifications (n: Nat) (events: List (Nat × Nat)) 
  (h1: 0 < n ∧ n ≤ 100)
  (h2: events.length > 0)
  (h3: ∀ e ∈ events, e.1 = 1 ∧ 1 ≤ e.2 ∧ e.2 ≤ 100) :
  List.get! (solve_thor_notifications n events) (solve_thor_notifications n events).length.pred = events.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem only_read_app_notifications (n: Nat) (events: List (Nat × Nat))
  (h1: 0 < n ∧ n ≤ 100)
  (h2: events.length > 0)
  (h3: ∀ e ∈ events, e.1 = 2 ∧ 1 ≤ e.2 ∧ e.2 ≤ 100) :
  ∀ count ∈ solve_thor_notifications n events, count = 0 := sorry

theorem unread_count_bounded (n: Nat) (events: List (Nat × Nat))
  (h1: 0 < n ∧ n ≤ 100)
  (h2: ∀ e ∈ events, e.1 = 1 ∧ 1 ≤ e.2 ∧ e.2 ≤ 100) :
  ∀ count ∈ solve_thor_notifications n events, 0 ≤ count ∧ count ≤ events.length := sorry
-- </vc-theorems>
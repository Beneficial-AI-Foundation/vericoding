-- <vc-preamble>
def list_sum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h :: t => h + list_sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_any (l : List Nat) (f : Nat → Bool) : Bool := sorry

def max_topics_prepared (N M S : Nat) (topic_hours : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_topics_non_negative (N M S : Nat) (topic_hours : List Nat) :
  N > 0 → M > 0 → S > 0 → S ≤ 16 → topic_hours.length > 0 →
  max_topics_prepared N M S topic_hours ≥ 0 :=
sorry

theorem max_topics_bounded_by_length (N M S : Nat) (topic_hours : List Nat) :
  N > 0 → M > 0 → S > 0 → S ≤ 16 → topic_hours.length > 0 →
  max_topics_prepared N M S topic_hours ≤ topic_hours.length :=
sorry

theorem max_topics_zero_when_s_too_large (N M S : Nat) (topic_hours : List Nat) :
  N > 0 → M > 0 → S ≥ 17 → topic_hours.length > 0 →
  max_topics_prepared N M S topic_hours = 0 :=
sorry

theorem max_topics_bounded_by_feasible (N M S : Nat) (topic_hours : List Nat) :
  N > 0 → M > 0 → S > 0 → S ≤ 16 → topic_hours.length > 0 →
  max_topics_prepared N M S topic_hours ≤
    (List.countP (fun h => h/S ≤ 2) topic_hours) :=
sorry
-- </vc-theorems>
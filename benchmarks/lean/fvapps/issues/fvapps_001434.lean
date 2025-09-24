-- <vc-preamble>
def sum (l: List Nat) : Nat :=
  l.foldl (· + ·) 0

def natToFloat (n : Nat) : Float :=
  Float.ofNat n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_class_stats (marks: List Nat) : Nat × Float × List Nat × List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_class_stats_backlog_matches_failing_count 
  (marks: List Nat) (h: marks.length > 0) (h2: ∀ x ∈ marks, x ≤ 100) :
  let (backlog, _, _, _) := calculate_class_stats marks
  backlog = (marks.filter (· < 31)).length := sorry

theorem calculate_class_stats_average_matches_passing_average
  (marks: List Nat) (h: marks.length > 0) (h2: ∀ x ∈ marks, x ≤ 100) :
  let (_, avg, _, _) := calculate_class_stats marks
  let passing := marks.filter (· ≥ 31)
  passing.isEmpty → avg = 0 ∧
  ¬passing.isEmpty → avg = natToFloat (sum passing) / natToFloat marks.length := sorry

theorem calculate_class_stats_toppers_correct
  (marks: List Nat) (h: marks.length > 0) (h2: ∀ x ∈ marks, x ≤ 100) :
  let (_, _, toppers, _) := calculate_class_stats marks
  let maxMark := marks.maximum?.getD 0
  toppers = (List.range marks.length).filter (fun i => 
    marks.get! i = maxMark) := sorry

theorem calculate_class_stats_diffs_correct
  (marks: List Nat) (h: marks.length > 0) (h2: ∀ x ∈ marks, x ≤ 100) :
  let (_, _, _, diffs) := calculate_class_stats marks
  let maxMark := marks.maximum?.getD 0
  diffs = marks.map (fun x => maxMark - x) := sorry

theorem calculate_class_stats_diffs_length
  (marks: List Nat) (h: marks.length > 0) (h2: ∀ x ∈ marks, x ≤ 100) :
  let (_, _, _, diffs) := calculate_class_stats marks
  diffs.length = marks.length := sorry
-- </vc-theorems>
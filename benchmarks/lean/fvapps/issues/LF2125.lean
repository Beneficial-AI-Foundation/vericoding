-- <vc-preamble>
def parseDateTime (s : String) : Option DateTime := sorry

/- Convert timestamp to datetime string -/

def formatDateTime (dt : DateTime) : String := sorry

/- Find first warning threshold function signature -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findFirstWarningThreshold (n m : Nat) (logs : List String) : String := sorry

theorem find_first_warning_result_format
  (n m : Nat) (logs : List String)
  (h1 : n > 0) (h2 : n ≤ 3600)
  (h3 : m > 0) (h4 : m ≤ 10)
  (h5 : logs.length > 0) (h6 : logs.length ≤ 20) :
  let result := findFirstWarningThreshold n m logs
  result = "-1" ∨ (∃ dt : DateTime, formatDateTime dt = result) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_first_warning_result_in_logs
  (n m : Nat) (logs : List String)
  (h1 : n > 0) (h2 : n ≤ 3600)
  (h3 : m > 0) (h4 : m ≤ 10)
  (h5 : logs.length > 0) (h6 : logs.length ≤ 20) :
  let result := findFirstWarningThreshold n m logs
  result = "-1" ∨ ∃ log ∈ logs, result.isPrefixOf log := sorry

theorem find_first_warning_window_count
  (n m : Nat) (logs : List String)
  (h1 : n > 0) (h2 : n ≤ 3600)
  (h3 : m > 0) (h4 : m ≤ 10)
  (h5 : logs.length > 0) (h6 : logs.length ≤ 20) :
  let result := findFirstWarningThreshold n m logs
  let resultDt := parseDateTime result
  match resultDt with
  | none => result = "-1"
  | some dt =>
    ∃ windowEvents : List String,
    windowEvents.length ≥ m ∧
    ∀ log ∈ windowEvents,
    match parseDateTime (log.take 19) with
    | some logDt => logDt.toNat - dt.toNat ≤ n
    | none => False := sorry

theorem find_first_warning_empty_cases
  (logs : List String)
  (h1 : logs.length > 0) (h2 : logs.length ≤ 20) :
  findFirstWarningThreshold 0 1 logs = "-1" := sorry

theorem find_first_warning_impossible_cases
  (n : Nat) (logs : List String)
  (h1 : logs.length > 0) (h2 : logs.length ≤ 20) :
  findFirstWarningThreshold n (logs.length + 1) logs = "-1" := sorry

/-
info: '2012-03-16 16:16:43'
-/
-- #guard_msgs in
-- #eval find_first_warning_threshold 60 3 ["2012-03-16 16:15:25: Disk size is", "2012-03-16 16:15:25: Network failute", "2012-03-16 16:16:29: Cant write varlog", "2012-03-16 16:16:42: Unable to start process", "2012-03-16 16:16:43: Disk size is too small", "2012-03-16 16:16:53: Timeout detected"]

/-
info: '-1'
-/
-- #guard_msgs in
-- #eval find_first_warning_threshold 1 2 ["2012-03-16 23:59:59:Disk size", "2012-03-17 00:00:00: Network", "2012-03-17 00:00:01:Cant write varlog"]

/-
info: '2012-03-17 00:00:00'
-/
-- #guard_msgs in
-- #eval find_first_warning_threshold 2 2 ["2012-03-16 23:59:59:Disk size is too sm", "2012-03-17 00:00:00:Network failute dete", "2012-03-17 00:00:01:Cant write varlogmysq"]
-- </vc-theorems>
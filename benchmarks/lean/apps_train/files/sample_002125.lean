/-
You've got a list of program warning logs. Each record of a log stream is a string in this format:  "2012-MM-DD HH:MM:SS:MESSAGE" (without the quotes). 

String "MESSAGE" consists of spaces, uppercase and lowercase English letters and characters "!", ".", ",", "?". String "2012-MM-DD" determines a correct date in the year of 2012. String "HH:MM:SS" determines a correct time in the 24 hour format.

The described record of a log stream means that at a certain time the record has got some program warning (string "MESSAGE" contains the warning's description).

Your task is to print the first moment of time, when the number of warnings for the last n seconds was not less than m.

-----Input-----

The first line of the input contains two space-separated integers n and m (1 ≤ n, m ≤ 10000).

The second and the remaining lines of the input represent the log stream. The second line of the input contains the first record of the log stream, the third line contains the second record and so on. Each record of the log stream has the above described format. All records are given in the chronological order, that is, the warning records are given in the order, in which the warnings appeared in the program. 

It is guaranteed that the log has at least one record. It is guaranteed that the total length of all lines of the log stream doesn't exceed 5·10^6 (in particular, this means that the length of some line does not exceed 5·10^6 characters). It is guaranteed that all given dates and times are correct, and the string 'MESSAGE" in all records is non-empty.

-----Output-----

If there is no sought moment of time, print -1. Otherwise print a string in the format "2012-MM-DD HH:MM:SS" (without the quotes) — the first moment of time when the number of warnings for the last n seconds got no less than m.

-----Examples-----
Input
60 3
2012-03-16 16:15:25: Disk size is
2012-03-16 16:15:25: Network failute
2012-03-16 16:16:29: Cant write varlog
2012-03-16 16:16:42: Unable to start process
2012-03-16 16:16:43: Disk size is too small
2012-03-16 16:16:53: Timeout detected

Output
2012-03-16 16:16:43

Input
1 2
2012-03-16 23:59:59:Disk size
2012-03-17 00:00:00: Network
2012-03-17 00:00:01:Cant write varlog

Output
-1

Input
2 2
2012-03-16 23:59:59:Disk size is too sm
2012-03-17 00:00:00:Network failute dete
2012-03-17 00:00:01:Cant write varlogmysq

Output
2012-03-17 00:00:00
-/

def parseDateTime (s : String) : Option DateTime := sorry

/- Convert timestamp to datetime string -/

def formatDateTime (dt : DateTime) : String := sorry

/- Find first warning threshold function signature -/

-- <vc-helpers>
-- </vc-helpers>

def findFirstWarningThreshold (n m : Nat) (logs : List String) : String := sorry

theorem find_first_warning_result_format
  (n m : Nat) (logs : List String)
  (h1 : n > 0) (h2 : n ≤ 3600)
  (h3 : m > 0) (h4 : m ≤ 10)
  (h5 : logs.length > 0) (h6 : logs.length ≤ 20) :
  let result := findFirstWarningThreshold n m logs
  result = "-1" ∨ (∃ dt : DateTime, formatDateTime dt = result) := sorry

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

-- Apps difficulty: competition
-- Assurance level: unguarded
/-
You are provided with the marks of entire class in Data structures exam out of 100. You need to calculate the number of students having backlog (passing marks is >=31) and the average of the class. But this average is not a normal average, for this average marks of students having backlog are not considered but they will be considered in number of students. Also print the index of topper’s marks and print the difference of everyone’s marks with respect to the topper. 
In first line print the number of students having backlog and average of the class. In second line print indices of all the toppers(in case of more than 1 topper print index of all toppers in reverse order). Next N lines print the difference of everyone’s marks with respect to topper(s).
Note- if all students have backlog than average will be 0.
INPUT
The first line of the input contains an integer T denoting the number of test cases.
Next line contains N denoting the no of students in the class.
The line contains N space seprated integers A1,A2,A3….AN denoting the marks of each student in exam.
OUTPUT
First line contains the number of students having backlog and the special average of marks as described above. Average must have 2 decimal places.
Next line contains the indices of all the toppers in given array in reverse order.
Next N lines contain the difference of every student’s marks with respect to toppers.
Constraints
1<= T <= 100
1<= N <= 30
0<= Ai<= 100
Example
Input
1
9
56 42 94 25 74 99 27 52 83
Output
2 55.55
5 
43
57
5
74
25
0
72
47
16
-/

def sum (l: List Nat) : Nat :=
  l.foldl (· + ·) 0

def natToFloat (n : Nat) : Float :=
  Float.ofNat n

-- <vc-helpers>
-- </vc-helpers>

def calculate_class_stats (marks: List Nat) : Nat × Float × List Nat × List Nat :=
  sorry

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

-- Apps difficulty: interview
-- Assurance level: guarded
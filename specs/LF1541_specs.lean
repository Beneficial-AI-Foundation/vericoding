-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_below_average_students (input : List (List String)) : List String := sorry

def sumList (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + sumList rest
-- </vc-definitions>

-- <vc-theorems>
theorem find_below_average_students_returns_below_average 
  (input : List (List String)) (result : List String) 
  (h : result = find_below_average_students input)
  (student : String) (h2 : student ∈ result) 
  (parsed := student.split (· == ' '))
  (marks := String.toNat! (parsed.get! 2))
  (input_head := input.head!)
  (student_records := input_head.tail!)
  (total_marks := sumList (student_records.map (fun s => String.toNat! ((s.split (· == ' ')).get! 2))))
  (avg := total_marks / student_records.length) :
  marks < avg := sorry

theorem find_below_average_students_valid_phone_numbers
  (input : List (List String)) (result : List String)
  (h : result = find_below_average_students input)
  (student : String) (h2 : student ∈ result) 
  (phone := (student.split (· == ' ')).get! 1) :
  phone.length = 10 ∧ phone.all Char.isDigit := sorry

theorem find_below_average_students_sorted_marks
  (input : List (List String)) (result : List String)
  (h : result = find_below_average_students input) :
  List.Pairwise (fun s1 s2 => 
    let marks1 := String.toNat! ((s1.split (· == ' ')).get! 2)
    let marks2 := String.toNat! ((s2.split (· == ' ')).get! 2)
    marks1 ≤ marks2
  ) result := sorry
-- </vc-theorems>
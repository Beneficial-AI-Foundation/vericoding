

// <vc-helpers>
function grade_to_letter(grade: real): string
  requires 0.0 <= grade <= 4.0
{
  if grade == 4.0 then "A+"
  else if grade > 3.7 then "A"
  else if grade > 3.3 then "A-"
  else if grade > 3.0 then "B+"
  else if grade > 2.7 then "B"
  else if grade > 2.3 then "B-"
  else if grade > 2.0 then "C+"
  else if grade > 1.7 then "C"
  else if grade > 1.3 then "C-"
  else if grade > 1.0 then "D+"
  else if grade > 0.7 then "D"
  else if grade > 0.0 then "D-"
  else "E"
}

lemma grade_to_letter_correctness(grade: real)
  requires 0.0 <= grade <= 4.0
  ensures grade == 4.0 ==> grade_to_letter(grade) == "A+"
  ensures grade < 4.0 && grade > 3.7 ==> grade_to_letter(grade) == "A"
  ensures grade <= 3.7 && grade > 3.3 ==> grade_to_letter(grade) == "A-"
  ensures grade <= 3.3 && grade > 3.0 ==> grade_to_letter(grade) == "B+"
  ensures grade <= 3.0 && grade > 2.7 ==> grade_to_letter(grade) == "B"
  ensures grade <= 2.7 && grade > 2.3 ==> grade_to_letter(grade) == "B-"
  ensures grade <= 2.3 && grade > 2.0 ==> grade_to_letter(grade) == "C+"
  ensures grade <= 2.0 && grade > 1.7 ==> grade_to_letter(grade) == "C"
  ensures grade <= 1.7 && grade > 1.3 ==> grade_to_letter(grade) == "C-"
  ensures grade <= 1.3 && grade > 1.0 ==> grade_to_letter(grade) == "D+"
  ensures grade <= 1.0 && grade > 0.7 ==> grade_to_letter(grade) == "D"
  ensures grade <= 0.7 && grade > 0.0 ==> grade_to_letter(grade) == "D-"
  ensures grade == 0.0 ==> grade_to_letter(grade) == "E"
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def numerical_letter_grade(grades: list[float]) -> list[str]
It is the last week of the semester and the teacher has to give the grades to students. The teacher has been making her own algorithm for grading. The only problem is, she has lost the code she used for grading. She has given you a list of GPAs for some students and you have to write a function that can output a list of letter grades using the following table: GPA       |    Letter grade 4.0                A+ > 3.7                A > 3.3                A- > 3.0                B+ > 2.7                B > 2.3                B- > 2.0                C+ > 1.7                C > 1.3                C- > 1.0                D+ > 0.7                D > 0.0                D- 0.0                E Note: I have included a hypothesis that Float is hashable, not sure if this will mess up proving attempts but we can modify it if so. Reviewer: please think if there's a better way. Example: grade_equation([4.0, 3, 1.7, 2, 3.5]) ==> ['A+', 'B', 'C-', 'C', 'A-']
*/
// </vc-description>

// <vc-spec>
method numerical_letter_grade(grades: seq<real>) returns (letters: seq<string>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |grades| ==> 0.0 <= grades[i] <= 4.0
  // pre-conditions-end
  // post-conditions-start
  ensures |letters| == |grades|
  ensures forall i :: 0 <= i < |grades| && grades[i] == 4.0 ==> letters[i] == "A+"
  ensures forall i :: 0 <= i < |grades| && grades[i] < 4.0 && grades[i] > 3.7 ==> letters[i] == "A"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 3.7 && grades[i] > 3.3 ==> letters[i] == "A-"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 3.3 && grades[i] > 3.0 ==> letters[i] == "B+"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 3.0 && grades[i] > 2.7 ==> letters[i] == "B"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 2.7 && grades[i] > 2.3 ==> letters[i] == "B-"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 2.3 && grades[i] > 2.0 ==> letters[i] == "C+"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 2.0 && grades[i] > 1.7 ==> letters[i] == "C"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 1.7 && grades[i] > 1.3 ==> letters[i] == "C-"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 1.3 && grades[i] > 1.0 ==> letters[i] == "D+"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 1.0 && grades[i] > 0.7 ==> letters[i] == "D"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 0.7 && grades[i] > 0.0 ==> letters[i] == "D-"
  ensures forall i :: 0 <= i < |grades| && grades[i] == 0.0 ==> letters[i] == "E"
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
  letters := [];
  var i := 0;
  while i < |grades|
    invariant 0 <= i <= |grades|
    invariant |letters| == i
    invariant forall j :: 0 <= j < i && grades[j] == 4.0 ==> letters[j] == "A+"
    invariant forall j :: 0 <= j < i && grades[j] < 4.0 && grades[j] > 3.7 ==> letters[j] == "A"
    invariant forall j :: 0 <= j < i && grades[j] <= 3.7 && grades[j] > 3.3 ==> letters[j] == "A-"
    invariant forall j :: 0 <= j < i && grades[j] <= 3.3 && grades[j] > 3.0 ==> letters[j] == "B+"
    invariant forall j :: 0 <= j < i && grades[j] <= 3.0 && grades[j] > 2.7 ==> letters[j] == "B"
    invariant forall j :: 0 <= j < i && grades[j] <= 2.7 && grades[j] > 2.3 ==> letters[j] == "B-"
    invariant forall j :: 0 <= j < i && grades[j] <= 2.3 && grades[j] > 2.0 ==> letters[j] == "C+"
    invariant forall j :: 0 <= j < i && grades[j] <= 2.0 && grades[j] > 1.7 ==> letters[j] == "C"
    invariant forall j :: 0 <= j < i && grades[j] <= 1.7 && grades[j] > 1.3 ==> letters[j] == "C-"
    invariant forall j :: 0 <= j < i && grades[j] <= 1.3 && grades[j] > 1.0 ==> letters[j] == "D+"
    invariant forall j :: 0 <= j < i && grades[j] <= 1.0 && grades[j] > 0.7 ==> letters[j] == "D"
    invariant forall j :: 0 <= j < i && grades[j] <= 0.7 && grades[j] > 0.0 ==> letters[j] == "D-"
    invariant forall j :: 0 <= j < i && grades[j] == 0.0 ==> letters[j] == "E"
  {
    var letter := grade_to_letter(grades[i]);
    grade_to_letter_correctness(grades[i]);
    letters := letters + [letter];
    i := i + 1;
  }
}
// </vc-code>


// <vc-helpers>
// Helper function to map a single GPA to a letter grade
function GetLetterGrade(gpa: real): string
{
  if gpa == 4.0 then "A+"
  else if gpa > 3.7 then "A"
  else if gpa > 3.3 then "A-"
  else if gpa > 3.0 then "B+"
  else if gpa > 2.7 then "B"
  else if gpa > 2.3 then "B-"
  else if gpa > 2.0 then "C+"
  else if gpa > 1.7 then "C"
  else if gpa > 1.3 then "C-"
  else if gpa > 1.0 then "D+"
  else if gpa > 0.7 then "D"
  else if gpa > 0.0 then "D-"
  else "E"
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def numerical_letter_grade(grades: list[float]) -> list[str]
It is the last week of the semester and the teacher has to give the grades to students. The teacher has been making her own algorithm for grading. The only problem is, she has lost the code she used for grading. She has given you a list of GPAs for some students and you have to write a function that can output a list of letter grades using the following table: GPA       |    Letter grade 4.0                A+ > 3.7                A > 3.3                A- > 3.0                B+ > 2.7                B > 2.3                B- > 2.0                C+ > 1.7                C > 1.3                C- > 1.0                D+ > 0.7                D > 0.0                D- 0.0                E Note: I have included a hypothesis that Float is hashable, not sure if this will mess up proving attempts but we can modify it if so. Reviewer: please think if there's a better way. Example: grade_equation([4.0, 3, 1.7, 2, 3.5]) ==> ['A+', 'B', 'C-', 'C', 'A-']
*/
// </vc-description>

// <vc-spec>
method NumericalLetterGrade(grades: seq<real>) returns (letterGrades: seq<string>)
  requires forall i :: 0 <= i < |grades| ==> grades[i] >= 0.0
  ensures |letterGrades| == |grades|
  ensures forall i :: 0 <= i < |grades| ==> letterGrades[i] == GetLetterGrade(grades[i])
// </vc-spec>
// <vc-code>
{
  letterGrades := [];
  for i := 0 to |grades|
    invariant 0 <= i <= |grades|
    invariant |letterGrades| == i
    invariant forall k :: 0 <= k < i ==> letterGrades[k] == GetLetterGrade(grades[k])
  {
    letterGrades := letterGrades + [GetLetterGrade(grades[i])];
  }
}
// </vc-code>

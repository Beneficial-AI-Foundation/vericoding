// <vc-preamble>

function getLetterGrade(gpa: real): string
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

predicate ValidLetterGrades(grades: seq<string>)
{
    forall grade :: grade in grades ==> grade in {"A+", "A", "A-", "B+", "B", "B-", "C+", "C", "C-", "D+", "D", "D-", "E"}
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numerical_letter_grade(grades: seq<real>) returns (letter_grades: seq<string>)
    ensures |letter_grades| == |grades|
    ensures forall i :: 0 <= i < |grades| ==> letter_grades[i] == getLetterGrade(grades[i])
    ensures ValidLetterGrades(letter_grades)
// </vc-spec>
// <vc-code>
{
  letter_grades := [];
  for i := 0 to |grades|
    invariant |letter_grades| == i
    invariant forall j :: 0 <= j < i ==> letter_grades[j] == getLetterGrade(grades[j])
    invariant ValidLetterGrades(letter_grades)
  {
    letter_grades := letter_grades + [getLetterGrade(grades[i])];
  }
}
// </vc-code>

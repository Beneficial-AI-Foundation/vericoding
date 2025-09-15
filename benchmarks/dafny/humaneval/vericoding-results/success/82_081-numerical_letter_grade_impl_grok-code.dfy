// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function GradeToLetter(grade: real): string
  requires 0.0 <= grade <= 4.0
  ensures grade == 4.0 ==> GradeToLetter(grade) == "A+"
  ensures grade < 4.0 && grade > 3.7 ==> GradeToLetter(grade) == "A"
  ensures grade <= 3.7 && grade > 3.3 ==> GradeToLetter(grade) == "A-"
  ensures grade <= 3.3 && grade > 3.0 ==> GradeToLetter(grade) == "B+"
  ensures grade <= 3.0 && grade > 2.7 ==> GradeToLetter(grade) == "B"
  ensures grade <= 2.7 && grade > 2.3 ==> GradeToLetter(grade) == "B-"
  ensures grade <= 2.3 && grade > 2.0 ==> GradeToLetter(grade) == "C+"
  ensures grade <= 2.0 && grade > 1.7 ==> GradeToLetter(grade) == "C"
  ensures grade <= 1.7 && grade > 1.3 ==> GradeToLetter(grade) == "C-"
  ensures grade <= 1.3 && grade > 1.0 ==> GradeToLetter(grade) == "D+"
  ensures grade <= 1.0 && grade > 0.7 ==> GradeToLetter(grade) == "D"
  ensures grade <= 0.7 && grade > 0.0 ==> GradeToLetter(grade) == "D-"
  ensures grade == 0.0 ==> GradeToLetter(grade) == "E"
{
  /* helper modified by LLM (iteration 2): fixed condition for grade A to use >3.7 instead of >=3.7 */
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
// </vc-helpers>

// <vc-spec>
method numerical_letter_grade(grades: seq<real>) returns (letters: seq<string>)

  requires forall i :: 0 <= i < |grades| ==> 0.0 <= grades[i] <= 4.0

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
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): no changes needed, implementation is correct */
  letters := [];
  var i := 0;
  while i < |grades| 
    invariant 0 <= i <= |grades|
    invariant |letters| == i
    invariant forall j :: 0 <= j < i ==> letters[j] == GradeToLetter(grades[j])
  {
    letters := letters + [GradeToLetter(grades[i])];
    i := i + 1;
  }
}
// </vc-code>

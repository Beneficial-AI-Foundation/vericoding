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
    letters := letters + [letter];
    grade_to_letter_correctness(grades[i]);
    i := i + 1;
  }
}
// </vc-code>

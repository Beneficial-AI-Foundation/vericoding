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
/* helper modified by LLM (iteration 5): prove getLetterGrade returns a valid grade */
lemma GetLetterGradeValid(g: real)
  ensures getLetterGrade(g) in {"A+", "A", "A-", "B+", "B", "B-", "C+", "C", "C-", "D+", "D", "D-", "E"}
{
  if g == 4.0 {
    assert getLetterGrade(g) == "A+";
  } else if g > 3.7 {
    assert getLetterGrade(g) == "A";
  } else if g > 3.3 {
    assert getLetterGrade(g) == "A-";
  } else if g > 3.0 {
    assert getLetterGrade(g) == "B+";
  } else if g > 2.7 {
    assert getLetterGrade(g) == "B";
  } else if g > 2.3 {
    assert getLetterGrade(g) == "B-";
  } else if g > 2.0 {
    assert getLetterGrade(g) == "C+";
  } else if g > 1.7 {
    assert getLetterGrade(g) == "C";
  } else if g > 1.3 {
    assert getLetterGrade(g) == "C-";
  } else if g > 1.0 {
    assert getLetterGrade(g) == "D+";
  } else if g > 0.7 {
    assert getLetterGrade(g) == "D";
  } else if g > 0.0 {
    assert getLetterGrade(g) == "D-";
  } else {
    assert getLetterGrade(g) == "E";
  }
  assert getLetterGrade(g) in {"A+", "A", "A-", "B+", "B", "B-", "C+", "C", "C-", "D+", "D", "D-", "E"};
}

/* helper modified by LLM (iteration 5): show sequence of mapped grades is valid */
lemma LetterGradesAreValidFromMapping(gr: seq<real>, lg: seq<string>)
  requires |gr| == |lg|
  requires forall i :: 0 <= i < |gr| ==> lg[i] == getLetterGrade(gr[i])
  ensures ValidLetterGrades(lg)
{
  var i := 0;
  while i < |gr|
    invariant 0 <= i <= |gr|
    invariant forall j :: 0 <= j < i ==> lg[j] in {"A+", "A", "A-", "B+", "B", "B-", "C+", "C", "C-", "D+", "D", "D-", "E"}
  {
    GetLetterGradeValid(gr[i]);
    assert lg[i] == getLetterGrade(gr[i]);
    assert getLetterGrade(gr[i]) in {"A+", "A", "A-", "B+", "B", "B-", "C+", "C", "C-", "D+", "D", "D-", "E"};
    i := i + 1;
  }
  assert forall k :: 0 <= k < |lg| ==> lg[k] in {"A+", "A", "A-", "B+", "B", "B-", "C+", "C", "C-", "D+", "D", "D-", "E"};
  assert ValidLetterGrades(lg);
}

// </vc-helpers>

// <vc-spec>
method numerical_letter_grade(grades: seq<real>) returns (letter_grades: seq<string>)
    ensures |letter_grades| == |grades|
    ensures forall i :: 0 <= i < |grades| ==> letter_grades[i] == getLetterGrade(grades[i])
    ensures ValidLetterGrades(letter_grades)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build letter grades and prove they are valid */
  var arr := new string[|grades|];
  var i := 0;
  while i < |grades|
    invariant 0 <= i <= |grades|
    invariant forall j :: 0 <= j < i ==> arr[j] == getLetterGrade(grades[j])
  {
    var g := grades[i];
    GetLetterGradeValid(g);
    arr[i] := getLetterGrade(g);
    i := i + 1;
  }
  letter_grades := arr[..];
  LetterGradesAreValidFromMapping(grades, letter_grades);
}

// </vc-code>

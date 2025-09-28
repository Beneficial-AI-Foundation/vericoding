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
function ValidGradesSet(): set<string>
{
  {"A+", "A", "A-", "B+", "B", "B-", "C+", "C", "C-", "D+", "D", "D-", "E"}
}

lemma GetLetterGradeIsValid(gpa: real)
  ensures getLetterGrade(gpa) in ValidGradesSet()
{
  if gpa == 4.0 {
    assert getLetterGrade(gpa) == "A+";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 3.7 {
    assert getLetterGrade(gpa) == "A";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 3.3 {
    assert getLetterGrade(gpa) == "A-";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 3.0 {
    assert getLetterGrade(gpa) == "B+";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 2.7 {
    assert getLetterGrade(gpa) == "B";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 2.3 {
    assert getLetterGrade(gpa) == "B-";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 2.0 {
    assert getLetterGrade(gpa) == "C+";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 1.7 {
    assert getLetterGrade(gpa) == "C";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 1.3 {
    assert getLetterGrade(gpa) == "C-";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 1.0 {
    assert getLetterGrade(gpa) == "D+";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 0.7 {
    assert getLetterGrade(gpa) == "D";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else if gpa > 0.0 {
    assert getLetterGrade(gpa) == "D-";
    assert getLetterGrade(gpa) in ValidGradesSet();
  } else {
    assert getLetterGrade(gpa) == "E";
    assert getLetterGrade(gpa) in ValidGradesSet();
  }
}

lemma ValidLetterGrades_fromIndexProperty(s: seq<string>)
  requires forall j :: 0 <= j < |s| ==> s[j] in ValidGradesSet()
  ensures ValidLetterGrades(s)
{
  forall grade | grade in s
    ensures grade in {"A+", "A", "A-", "B+", "B", "B-", "C+", "C", "C-", "D+", "D", "D-", "E"}
  {
    var k :| 0 <= k < |s| && s[k] == grade;
    assert s[k] in ValidGradesSet();
    assert grade == s[k];
  }
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
  var i := 0;
  letter_grades := [];
  while i < |grades|
    invariant 0 <= i <= |grades|
    invariant |letter_grades| == i
    invariant forall j :: 0 <= j < i ==> letter_grades[j] == getLetterGrade(grades[j])
    invariant forall j :: 0 <= j < i ==> letter_grades[j] in ValidGradesSet()
    decreases |grades| - i
  {
    var lg := getLetterGrade(grades[i]);
    GetLetterGradeIsValid(grades[i]);
    assert lg in ValidGradesSet();
    letter_grades := letter_grades + [lg];
    i := i + 1;
  }
  ValidLetterGrades_fromIndexProperty(letter_grades);
}
// </vc-code>

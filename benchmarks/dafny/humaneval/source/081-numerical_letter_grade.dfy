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
{
  // impl-start
  letters := [];
  var i := 0;
  while i < |grades|
    // invariants-start
    invariant 0 <= i <= |grades|
    invariant |letters| == i
    invariant forall j :: 0 <= j < i && grades[j] == 4.0 ==> letters[j] == "A+"
    invariant forall j :: 0 <= j < i && grades[j] < 4.0  && grades[j] > 3.7 ==> letters[j] == "A"
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
    // invariants-end
  {
    if grades[i] == 4.0 {
      letters := letters + ["A+"];
    } else if grades[i] > 3.7 {
      letters := letters + ["A"];
    } else if grades[i] > 3.3 {
      letters := letters + ["A-"];
    } else if grades[i] > 3.0 {
      letters := letters + ["B+"];
    } else if grades[i] > 2.7 {
      letters := letters + ["B"];
    } else if grades[i] > 2.3 {
      letters := letters + ["B-"];
    } else if grades[i] > 2.0 {
      letters := letters + ["C+"];
    } else if grades[i] > 1.7 {
      letters := letters + ["C"];
    } else if grades[i] > 1.3 {
      letters := letters + ["C-"];
    } else if grades[i] > 1.0 {
      letters := letters + ["D+"];
    } else if grades[i] > 0.7 {
      letters := letters + ["D"];
    } else if grades[i] > 0.0 {
      letters := letters + ["D-"];
    } else {
      letters := letters + ["E"];
    }

    i := i + 1;
  }
  // impl-end
}

// <vc-helpers>
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
  var result: seq<string> := [];
  for i := 0 to |grades|
    invariant |result| == i
    invariant forall j :: 0 <= j < i && grades[j] == 4.0 ==> result[j] == "A+"
    invariant forall j :: 0 <= j < i && grades[j] < 4.0 && grades[j] > 3.7 ==> result[j] == "A"
    invariant forall j :: 0 <= j < i && grades[j] <= 3.7 && grades[j] > 3.3 ==> result[j] == "A-"
    invariant forall j :: 0 <= j < i && grades[j] <= 3.3 && grades[j] > 3.0 ==> result[j] == "B+"
    invariant forall j :: 0 <= j < i && grades[j] <= 3.0 && grades[j] > 2.7 ==> result[j] == "B"
    invariant forall j :: 0 <= j < i && grades[j] <= 2.7 && grades[j] > 2.3 ==> result[j] == "B-"
    invariant forall j :: 0 <= j < i && grades[j] <= 2.3 && grades[j] > 2.0 ==> result[j] == "C+"
    invariant forall j :: 0 <= j < i && grades[j] <= 2.0 && grades[j] > 1.7 ==> result[j] == "C"
    invariant forall j :: 0 <= j < i && grades[j] <= 1.7 && grades[j] > 1.3 ==> result[j] == "C-"
    invariant forall j :: 0 <= j < i && grades[j] <= 1.3 && grades[j] > 1.0 ==> result[j] == "D+"
    invariant forall j :: 0 <= j < i && grades[j] <= 1.0 && grades[j] > 0.7 ==> result[j] == "D"
    invariant forall j :: 0 <= j < i && grades[j] <= 0.7 && grades[j] > 0.0 ==> result[j] == "D-"
    invariant forall j :: 0 <= j < i && grades[j] == 0.0 ==> result[j] == "E"
  {
    var grade := grades[i];
    var letter: string;
    if grade == 4.0 {
      letter := "A+";
    } else if grade > 3.7 {
      letter := "A";
    } else if grade > 3.3 {
      letter := "A-";
    } else if grade > 3.0 {
      letter := "B+";
    } else if grade > 2.7 {
      letter := "B";
    } else if grade > 2.3 {
      letter := "B-";
    } else if grade > 2.0 {
      letter := "C+";
    } else if grade > 1.7 {
      letter := "C";
    } else if grade > 1.3 {
      letter := "C-";
    } else if grade > 1.0 {
      letter := "D+";
    } else if grade > 0.7 {
      letter := "D";
    } else if grade > 0.0 {
      letter := "D-";
    } else {
      letter := "E";
    }
    result := result + [letter];
  }
  return result;
}
// </vc-code>

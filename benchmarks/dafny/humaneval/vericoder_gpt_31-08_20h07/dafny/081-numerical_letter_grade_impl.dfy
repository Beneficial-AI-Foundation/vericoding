

// <vc-helpers>
// no helpers needed
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
  var res: seq<string> := [];
  var i: int := 0;
  while i < |grades|
    invariant 0 <= i <= |grades|
    invariant |res| == i
    invariant forall j :: 0 <= j < i && grades[j] == 4.0 ==> res[j] == "A+"
    invariant forall j :: 0 <= j < i && grades[j] < 4.0 && grades[j] > 3.7 ==> res[j] == "A"
    invariant forall j :: 0 <= j < i && grades[j] <= 3.7 && grades[j] > 3.3 ==> res[j] == "A-"
    invariant forall j :: 0 <= j < i && grades[j] <= 3.3 && grades[j] > 3.0 ==> res[j] == "B+"
    invariant forall j :: 0 <= j < i && grades[j] <= 3.0 && grades[j] > 2.7 ==> res[j] == "B"
    invariant forall j :: 0 <= j < i && grades[j] <= 2.7 && grades[j] > 2.3 ==> res[j] == "B-"
    invariant forall j :: 0 <= j < i && grades[j] <= 2.3 && grades[j] > 2.0 ==> res[j] == "C+"
    invariant forall j :: 0 <= j < i && grades[j] <= 2.0 && grades[j] > 1.7 ==> res[j] == "C"
    invariant forall j :: 0 <= j < i && grades[j] <= 1.7 && grades[j] > 1.3 ==> res[j] == "C-"
    invariant forall j :: 0 <= j < i && grades[j] <= 1.3 && grades[j] > 1.0 ==> res[j] == "D+"
    invariant forall j :: 0 <= j < i && grades[j] <= 1.0 && grades[j] > 0.7 ==> res[j] == "D"
    invariant forall j :: 0 <= j < i && grades[j] <= 0.7 && grades[j] > 0.0 ==> res[j] == "D-"
    invariant forall j :: 0 <= j < i && grades[j] == 0.0 ==> res[j] == "E"
  {
    assert 0 <= i < |grades|;
    var g := grades[i];
    assert 0.0 <= g <= 4.0;
    var s: string;
    if g == 4.0 then s := "A+"
    else if g < 4.0 && g > 3.7 then s := "A"
    else if g <= 3.7 && g > 3.3 then s := "A-"
    else if g <= 3.3 && g > 3.0 then s := "B+"
    else if g <= 3.0 && g > 2.7 then s := "B"
    else if g <= 2.7 && g > 2.3 then s := "B-"
    else if g <= 2.3 && g > 2.0 then s := "C+"
    else if g <= 2.0 && g > 1.7 then s := "C"
    else if g <= 1.7 && g > 1.3 then s := "C-"
    else if g <= 1.3 && g > 1.0 then s := "D+"
    else if g <= 1.0 && g > 0.7 then s := "D"
    else if g <= 0.7 && g > 0.0 then s := "D-"
    else s := "E";
    res := res + [s];
    i := i + 1;
  }
  letters := res;
}
// </vc-code>


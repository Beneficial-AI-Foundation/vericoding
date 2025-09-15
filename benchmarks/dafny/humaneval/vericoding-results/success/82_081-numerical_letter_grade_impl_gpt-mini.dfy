

// <vc-helpers>
function letter_of(g: real): string
  requires 0.0 <= g <= 4.0
{
  if g == 4.0 then "A+"
  else if g < 4.0 && g > 3.7 then "A"
  else if g <= 3.7 && g > 3.3 then "A-"
  else if g <= 3.3 && g > 3.0 then "B+"
  else if g <= 3.0 && g > 2.7 then "B"
  else if g <= 2.7 && g > 2.3 then "B-"
  else if g <= 2.3 && g > 2.0 then "C+"
  else if g <= 2.0 && g > 1.7 then "C"
  else if g <= 1.7 && g > 1.3 then "C-"
  else if g <= 1.3 && g > 1.0 then "D+"
  else if g <= 1.0 && g > 0.7 then "D"
  else if g <= 0.7 && g > 0.0 then "D-"
  else "E"
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
  var a := new string[|grades|];
  var i := 0;
  while i < |grades|
    invariant 0 <= i <= |grades|
    invariant forall j :: 0 <= j < i ==> a[j] == letter_of(grades[j])
    decreases |grades| - i
  {
    var g := grades[i];
    a[i] := letter_of(g);
    i := i + 1;
  }
  letters := a[..];
}
// </vc-code>


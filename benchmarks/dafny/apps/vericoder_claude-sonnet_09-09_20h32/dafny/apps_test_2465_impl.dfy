predicate ValidInput(angles: seq<int>)
{
  forall i :: 0 <= i < |angles| ==> 1 <= angles[i] < 180
}

function ComputeAnswer(angle: int): int
  requires 1 <= angle < 180
{
  var g := gcd(angle, 180);
  var de_over_g := angle / g;
  var n180_over_g := 180 / g;
  if de_over_g == n180_over_g - 1 then n180_over_g * 2 else n180_over_g
}

predicate CorrectOutput(angles: seq<int>, result: seq<int>)
  requires ValidInput(angles)
{
  |result| == |angles| &&
  forall i :: 0 <= i < |angles| ==> result[i] == ComputeAnswer(angles[i])
}

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

lemma ValidInputElement(angles: seq<int>, i: int)
  requires ValidInput(angles)
  requires 0 <= i < |angles|
  ensures 1 <= angles[i] < 180
{
}

lemma PreservesValidInput(angles: seq<int>, i: int)
  requires ValidInput(angles)
  requires 0 <= i <= |angles|
  ensures ValidInput(angles[0..i])
{
}

lemma CorrectOutputPrefix(angles: seq<int>, result: seq<int>, i: int)
  requires ValidInput(angles)
  requires 0 <= i <= |angles|
  requires |result| == i
  requires forall j :: 0 <= j < i ==> result[j] == ComputeAnswer(angles[j])
  ensures |result| == |angles[0..i]|
  ensures forall j :: 0 <= j < |angles[0..i]| ==> result[j] == ComputeAnswer(angles[0..i][j])
{
  assert angles[0..i] == angles[0..i];
  forall j | 0 <= j < i
    ensures result[j] == ComputeAnswer(angles[0..i][j])
  {
    assert angles[0..i][j] == angles[j];
  }
}

lemma GcdNonZero(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
{
}

lemma GcdDivides(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases a + b
{
  var g := gcd(a, b);
  if a == b {
    assert g == a;
  } else if a > b {
    GcdDivides(a - b, b);
    assert gcd(a - b, b) == g;
    assert (a - b) % g == 0;
    assert b % g == 0;
  } else {
    GcdDivides(a, b - a);
    assert gcd(a, b - a) == g;
    assert a % g == 0;
    assert (b - a) % g == 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(angles: seq<int>) returns (result: seq<int>)
  requires ValidInput(angles)
  ensures CorrectOutput(angles, result)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |angles|
    invariant 0 <= i <= |angles|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == ComputeAnswer(angles[j])
  {
    ValidInputElement(angles, i);
    GcdNonZero(angles[i], 180);
    GcdDivides(angles[i], 180);
    var answer := ComputeAnswer(angles[i]);
    result := result + [answer];
    i := i + 1;
  }
}
// </vc-code>


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
  requires a >= 0 && b >= 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

lemma gcdPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
{
  if b == 0 {
    assert gcd(a, b) == a;
  } else {
    gcdPositive(b, a % b);
  }
}

lemma gcdDivides(a: int, b: int)
  requires a >= 0 && b >= 0
  requires gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
{
  if b == 0 {
    assert gcd(a, b) == a;
  } else {
    gcdDivides(b, a % b);
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
    var angle := angles[i];
    var g := gcd(angle, 180);
    gcdPositive(angle, 180);
    gcdDivides(angle, 180);
    var de_over_g := angle / g;
    var n180_over_g := 180 / g;
    var answer := if de_over_g == n180_over_g - 1 then n180_over_g * 2 else n180_over_g;
    result := result + [answer];
    i := i + 1;
  }
}
// </vc-code>


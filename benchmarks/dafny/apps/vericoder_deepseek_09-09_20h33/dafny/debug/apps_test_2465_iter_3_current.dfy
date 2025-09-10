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
function gcd(a: nat, b: nat): nat
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then
    a
  else if a > b then
    gcd(a - b, b)
  else
    gcd(a, b - a)
}

lemma gcd_pos(a: nat, b: nat)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  decreases a + b
{
  if a == b {
  } else if a > b {
    gcd_pos(a - b, b);
  } else {
    gcd_pos(a, b - a);
  }
}

lemma gcd_division(a: nat, b: nat, g: nat)
  requires a > 0 && b > 0
  requires g == gcd(a, b)
  ensures a % g == 0 && b % g == 0
  decreases a + b
{
  if a == b {
  } else if a > b {
    gcd_division(a - b, b, g);
  } else {
    gcd_division(a, b - a, g);
  }
}
// </vc-helpers>
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
    invariant forall j :: 0 <= j < |angles| ==> 1 <= angles[j] < 180
  {
    var angle := angles[i];
    var g := gcd(angle, 180);
    gcd_pos(angle, 180);
    assert g > 0;
    gcd_division(angle, 180, g);
    
    var de_over_g := angle / g;
    var n180_over_g := 180 / g;
    if de_over_g == n180_over_g - 1 {
      result := result + [n180_over_g * 2];
    } else {
      result := result + [n180_over_g];
    }
    i := i + 1;
  }
}
// </vc-code>


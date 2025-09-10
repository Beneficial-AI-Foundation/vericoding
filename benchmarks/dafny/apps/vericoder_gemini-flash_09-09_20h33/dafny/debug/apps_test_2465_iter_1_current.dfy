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
  ensures (a == 0 && b == 0) ==> (gcd(a, b) == 0)
  ensures (a == 0 && b != 0) ==> (gcd(a, b) == b)
  ensures (a != 0 && b == 0) ==> (gcd(a, b) == a)
  ensures (a > 0 && b > 0) ==> (a % gcd(a, b) == 0 && b % gcd(a, b) == 0)
  ensures (a > 0 && b > 0) ==> forall d | d > 0 && a % d == 0 && b % d == 0 :: d <= gcd(a, b)
{
  if b == 0 then a else gcd(b, a % b)
}

lemma ComputeAnswer_properties(angle: int)
  requires 1 <= angle < 180
  ensures ComputeAnswer(angle) > 0
{
  var g := gcd(angle, 180);
  assert g > 0; // gcd of positive numbers is positive
  var de_over_g := angle / g;
  var n180_over_g := 180 / g;
  assert n180_over_g > 0; // 180/g must be positive since 180 > 0 and g > 0
}
// </vc-helpers>

// <vc-spec>
method solve(angles: seq<int>) returns (result: seq<int>)
  requires ValidInput(angles)
  ensures CorrectOutput(angles, result)
// </vc-spec>
// <vc-code>
{
    var n := |angles>;
    var result_array := new int[n];

    forall i | 0 <= i < n
      ensures result_array[i] == ComputeAnswer(angles[i])
    {
        result_array[i] := ComputeAnswer(angles[i]);
    }
    return result_array;
}
// </vc-code>


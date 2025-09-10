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
  requires a >= 0 && b >= 0 && (a > 0 || b > 0)
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

lemma GcdDivides(a: int, b: int)
  requires a >= 0 && b >= 0 && (a > 0 || b > 0)
  ensures var g := gcd(a, b); g >= 1 && g divides a && g divides b
{
  if b == 0 {
  } else {
    GcdDivides(b, a % b);
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
  for i := 0 to |angles| {
    assert ValidInput(angles);
    calc {
      ComputeAnswer(angles[i]);  // To help verify the computation
    }
    var temp := ComputeAnswer(angles[i]);
    result := result + [temp];
    assert |result| == i + 1;
    assert result[i] == temp;
    if i > 0 {
      assert forall j :: 0 <= j < i ==> result[j] == ComputeAnswer(angles[j]);
    }
  }
}
// </vc-code>


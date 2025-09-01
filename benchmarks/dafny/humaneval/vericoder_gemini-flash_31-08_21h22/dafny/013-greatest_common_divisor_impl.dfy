// recursive version should be more promising

// <vc-helpers>
lemma GCDProperty(a: int, b: int)
  requires b != 0
  ensures (a % b == 0) ==> (a / b) * b == a
  ensures (a % b != 0) ==> (a % b) > 0 || (a % b) < 0
{
}

lemma EuclideanAlgorithmTermination(a: int, b: int)
    decreases b
    ensures b == 0 ==> true
    ensures b != 0 ==> |a % b| < |b|
{}
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)
    // pre-conditions-start
    requires a != 0 || b != 0
    // pre-conditions-end
    // post-conditions-start
    ensures gcd != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if b == 0 then {
    return if a < 0 then -a else a;
  } else {
    GhostCall GCDProperty(a,b);
    GhostCall EuclideanAlgorithmTermination(a,b);
    return greatest_common_divisor(b, a % b);
  }
}
// </vc-code>


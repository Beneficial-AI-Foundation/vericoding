// <vc-preamble>
// Method to multiply a Legendre series by x
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LegendreMultiplyByX(c: seq<real>) returns (result: seq<real>)
  requires |c| > 0
  ensures |result| == |c| + 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): added loop invariant to prove postcondition */
  var res: seq<real> := [];
  var k: int := 0;
  while k <= |c|
    invariant 0 <= k <= |c| + 1 && |res| == k
  {
    var contribution1: real := if k > 0 then c[k-1] * (k as real) / ((2 * k - 1) as real) else 0.0;
    var contribution2: real := if k + 1 < |c| then c[k+1] * ((k+1) as real) / ((2*k + 3) as real) else 0.0;
    res := res + [contribution1 + contribution2];
    k := k + 1;
  }
  result := res;
}
// </vc-code>

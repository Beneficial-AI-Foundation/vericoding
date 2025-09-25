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
  assume {:axiom} false;
}
// </vc-code>

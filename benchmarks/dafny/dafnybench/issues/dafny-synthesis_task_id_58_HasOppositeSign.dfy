// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method HasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
// </vc-spec>
// <vc-code>
{
  result := (a < 0 && b > 0) || (a > 0 && b < 0);
}
// </vc-code>

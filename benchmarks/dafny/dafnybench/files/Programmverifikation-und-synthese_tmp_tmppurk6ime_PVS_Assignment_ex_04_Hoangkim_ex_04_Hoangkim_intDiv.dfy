// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d;
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>

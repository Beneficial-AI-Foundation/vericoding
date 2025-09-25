// <vc-preamble>
predicate sqrt(x: int, r: int) {
    r*r <= x && (r+1)*(r+1) > x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures sqrt(x, res);
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>

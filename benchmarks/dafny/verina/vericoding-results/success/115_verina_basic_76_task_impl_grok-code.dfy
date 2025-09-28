// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MyMin(x: int, y: int) returns (result: int)
    ensures (x <= y ==> result == x) && (x > y ==> result == y)
// </vc-spec>
// <vc-code>
{
  result := if x < y then x else y;
}
// </vc-code>

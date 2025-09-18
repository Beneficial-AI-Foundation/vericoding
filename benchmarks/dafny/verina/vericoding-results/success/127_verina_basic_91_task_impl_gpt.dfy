// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSwap(x: int, y: int, r: (int, int)) { r.0 == y && r.1 == x }
// </vc-helpers>

// <vc-spec>
method Swap(x: int, y: int) returns (result: (int, int))
    ensures
        result.0 == y &&
        result.1 == x &&
        (x != y ==> result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
{
  result := (y, x);
}
// </vc-code>

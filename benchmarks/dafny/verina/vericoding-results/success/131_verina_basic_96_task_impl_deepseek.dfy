// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma SwapSimultaneousLemma(x: int, y: int) ensures (y, x).0 == y && (y, x).1 == x && (x != y ==> (y, x).0 != x && (y, x).1 != y) { }
// </vc-helpers>

// <vc-spec>
method SwapSimultaneous(x: int, y: int) returns (result: (int, int))
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

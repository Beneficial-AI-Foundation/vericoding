// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SwapPair(a: int, b: int): (int, int) { (b, a) }

lemma SwapDistinctPreserved(x: int, y: int) ensures x != y ==> SwapPair(x,y).0 != x && SwapPair(x,y).1 != y { }
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

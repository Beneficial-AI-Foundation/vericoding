// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function swap(a: int, b: int): (int, int) { (b, a) }
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
    result := swap(x, y);
}
// </vc-code>

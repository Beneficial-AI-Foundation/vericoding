// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SwapBitvectors(x: int, y: int) returns (result: (int, int))
    requires 0 <= x < 256 && 0 <= y < 256
    ensures result.0 == y && result.1 == x
    ensures x != y ==> (result.0 != x && result.1 != y)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Removed XOR operations on `int` types, as these are compilation errors in Dafny. Implemented direct assignment to achieve the swap. */
{
    return (y, x);
}
// </vc-code>

// <vc-preamble>
function IntMax(x: int, y: int): int
{
    if x < y then y else x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(a: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= a.Length
// </vc-spec>
// <vc-code>
{
    // TODO: implement
    result := 0;
}
// </vc-code>

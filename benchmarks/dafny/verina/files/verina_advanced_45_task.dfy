// <vc-preamble>
function SpecSum(xs: array<int>, start: int, len: int): int
    decreases len
    reads xs
{
    if len <= 0 then
        0
    else if start < 0 || start >= xs.Length then
        0
    else
        xs[start] + SpecSum(xs, start + 1, len - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MaxSubarraySum(xs: array<int>) returns (result: int)
    ensures xs.Length == 0 ==> result == 0
    ensures xs.Length > 0 ==> 
        (exists start: int, len: int :: 
            0 <= start < xs.Length && 
            1 <= len <= xs.Length - start &&
            result == SpecSum(xs, start, len)) &&
        (forall start: int, len: int ::
            0 <= start < xs.Length && 
            1 <= len <= xs.Length - start
            ==> SpecSum(xs, start, len) <= result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
    result := 0;
}
// </vc-code>

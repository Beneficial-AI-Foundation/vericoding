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
/* helper modified by LLM (iteration 5): added decreases clause to fix termination */
lemma SpecSumProperty(xs: array<int>, start: int, len: int)
    requires 0 <= start < xs.Length
    requires 1 <= len <= xs.Length - start
    ensures SpecSum(xs, start, len) == xs[start] + SpecSum(xs, start + 1, len - 1)
{
}

function ComputeSum(xs: array<int>, start: int, len: int): int
    requires 0 <= start <= xs.Length
    requires 0 <= len <= xs.Length - start
    decreases len
    reads xs
{
    if len <= 0 then
        0
    else if start >= xs.Length then
        0
    else
        xs[start] + ComputeSum(xs, start + 1, len - 1)
}
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
    /* code modified by LLM (iteration 5): added ghost variables and assertions to prove postconditions */
    if xs.Length == 0 {
        result := 0;
        return;
    }
    
    result := xs[0];
    ghost var bestStart := 0;
    ghost var bestLen := 1;
    
    var i := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= bestStart < xs.Length
        invariant 1 <= bestLen <= xs.Length - bestStart
        invariant result == SpecSum(xs, bestStart, bestLen)
        invariant forall s: int, l: int :: 
            0 <= s < xs.Length && 1 <= l <= xs.Length - s && s < i
            ==> SpecSum(xs, s, l) <= result
    {
        var j := i;
        while j < xs.Length
            invariant i <= j <= xs.Length
            invariant 0 <= bestStart < xs.Length
            invariant 1 <= bestLen <= xs.Length - bestStart
            invariant result == SpecSum(xs, bestStart, bestLen)
            invariant forall s: int, l: int :: 
                0 <= s < xs.Length && 1 <= l <= xs.Length - s && 
                (s < i || (s == i && l <= j - i))
                ==> SpecSum(xs, s, l) <= result
        {
            var currentSum := SpecSum(xs, i, j - i + 1);
            if currentSum > result {
                result := currentSum;
                bestStart := i;
                bestLen := j - i + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

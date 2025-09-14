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
/* helper modified by LLM (iteration 3): added helper to prove existence and optimality properties */
lemma SpecSumProperty(xs: array<int>, start: int, len: int)
    requires 0 <= start < xs.Length
    requires 1 <= len <= xs.Length - start
    ensures SpecSum(xs, start, len) == xs[start] + SpecSum(xs, start + 1, len - 1)
{
}

lemma ExistsMaxSubarray(xs: array<int>, maxSum: int)
    requires xs.Length > 0
    requires forall start: int, len: int :: 0 <= start < xs.Length && 1 <= len <= xs.Length - start ==> SpecSum(xs, start, len) <= maxSum
    requires exists start: int, len: int :: 0 <= start < xs.Length && 1 <= len <= xs.Length - start && SpecSum(xs, start, len) == maxSum
    ensures exists start: int, len: int :: 0 <= start < xs.Length && 1 <= len <= xs.Length - start && maxSum == SpecSum(xs, start, len)
    ensures forall start: int, len: int :: 0 <= start < xs.Length && 1 <= len <= xs.Length - start ==> SpecSum(xs, start, len) <= maxSum
{
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
    /* code modified by LLM (iteration 3): track witness for existence proof and ensure proper postcondition satisfaction */
    if xs.Length == 0 {
        result := 0;
        return;
    }
    
    result := SpecSum(xs, 0, 1);
    ghost var witnessStart := 0;
    ghost var witnessLen := 1;
    
    for i := 0 to xs.Length
        invariant 0 <= i <= xs.Length
        invariant exists start: int, len: int :: 0 <= start < xs.Length && 1 <= len <= xs.Length - start && result == SpecSum(xs, start, len)
        invariant forall start: int, len: int :: 0 <= start < i && 1 <= len <= xs.Length - start ==> SpecSum(xs, start, len) <= result
    {
        for j := i + 1 to xs.Length + 1
            invariant i + 1 <= j <= xs.Length + 1
            invariant exists start: int, len: int :: 0 <= start < xs.Length && 1 <= len <= xs.Length - start && result == SpecSum(xs, start, len)
            invariant forall start: int, len: int :: 0 <= start < i && 1 <= len <= xs.Length - start ==> SpecSum(xs, start, len) <= result
            invariant forall len: int :: 1 <= len < j - i && len <= xs.Length - i ==> SpecSum(xs, i, len) <= result
        {
            var len := j - i;
            if len >= 1 && len <= xs.Length - i {
                var sum := SpecSum(xs, i, len);
                if sum > result {
                    result := sum;
                    witnessStart := i;
                    witnessLen := len;
                }
            }
        }
    }
    
    ExistsMaxSubarray(xs, result);
}
// </vc-code>

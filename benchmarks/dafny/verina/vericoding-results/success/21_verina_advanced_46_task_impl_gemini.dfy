// <vc-preamble>
function SubarraySum(numbers: array<int>, start: int, end: int): int
    requires 0 <= start <= end <= numbers.Length
    reads numbers
    decreases end - start
{
    if start == end then 0
    else numbers[start] + SubarraySum(numbers, start + 1, end)
}
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }

/* helper modified by LLM (iteration 3): no changes, compilation errors were in other helpers */
function MaxSumEndingAt(numbers: array<int>, k: int): int
    requires 0 <= k <= numbers.Length
    reads numbers
    decreases k
{
    if k == 0 then 0
    else max(0, MaxSumEndingAt(numbers, k - 1) + numbers[k - 1])
}

/* helper modified by LLM (iteration 3): no changes, compilation errors were in other helpers */
function MaxSumUpto(numbers: array<int>, k: int): int
    requires 0 <= k <= numbers.Length
    reads numbers
    decreases k
{
    if k == 0 then 0
    else max(MaxSumUpto(numbers, k - 1), MaxSumEndingAt(numbers, k))
}

/* helper modified by LLM (iteration 3): removed invalid reads clause */
lemma SubarraySumAppend(a: array<int>, start: int, end: int)
    requires 0 <= start < end <= a.Length
    ensures SubarraySum(a, start, end) == SubarraySum(a, start, end - 1) + a[end - 1]
    decreases end - start
{
    if start < end - 1 {
        SubarraySumAppend(a, start + 1, end);
    }
}

/* helper modified by LLM (iteration 3): removed invalid reads clause */
lemma KadaneProperties(numbers: array<int>, k: int)
    requires 0 <= k <= numbers.Length
    ensures MaxSumUpto(numbers, k) >= 0
    ensures forall start, end :: 0 <= start <= end <= k ==> SubarraySum(numbers, start, end) <= MaxSumUpto(numbers, k)
    ensures forall i :: 0 <= i <= k ==> SubarraySum(numbers, i, k) <= MaxSumEndingAt(numbers, k)
    decreases k
{
    if k > 0 {
        KadaneProperties(numbers, k - 1);
        forall i | 0 <= i < k {
            SubarraySumAppend(numbers, i, k);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method MaxSubarraySum(numbers: array<int>) returns (result: int)
    ensures result >= 0
    ensures forall start: int, end: int :: 
        start <= end && 0 <= start && end <= numbers.Length
        ==> SubarraySum(numbers, start, end) <= result
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): no changes, fix was in helpers */
    result := 0;
    var max_ending_here := 0;
    var i := 0;
    while i < numbers.Length
        invariant 0 <= i <= numbers.Length
        invariant max_ending_here == MaxSumEndingAt(numbers, i)
        invariant result == MaxSumUpto(numbers, i)
    {
        max_ending_here := max(0, max_ending_here + numbers[i]);
        result := max(result, max_ending_here);
        i := i + 1;
    }
    KadaneProperties(numbers, numbers.Length);
}
// </vc-code>

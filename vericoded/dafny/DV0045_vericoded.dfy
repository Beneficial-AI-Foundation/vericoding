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
lemma SubarraySumNonNegative(numbers: array<int>, start: int, end: int)
    requires 0 <= start <= end <= numbers.Length
    requires forall i :: start <= i < end ==> numbers[i] >= 0
    ensures SubarraySum(numbers, start, end) >= 0
    decreases end - start
{
    if start < end {
        SubarraySumNonNegative(numbers, start + 1, end);
    }
}

lemma SubarraySumEmpty(numbers: array<int>)
    ensures SubarraySum(numbers, 0, 0) == 0
{
}

/* helper modified by LLM (iteration 3): added comprehensive lemma for subarray sum properties */
lemma SubarraySumProperties(numbers: array<int>, i: int, j: int)
    requires 0 <= i <= numbers.Length
    requires 0 <= j <= i
    ensures forall start: int, end: int :: 
        start <= end && 0 <= start && end <= i && start >= j
        ==> SubarraySum(numbers, start, end) <= SubarraySum(numbers, start, end)
{
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
    /* code modified by LLM (iteration 3): fixed loop bounds and invariants to properly handle subarray enumeration */
    result := 0;
    
    var i := 0;
    while i <= numbers.Length
        invariant 0 <= i <= numbers.Length + 1
        invariant result >= 0
        invariant forall start: int, end: int :: 
            start <= end && 0 <= start && end <= numbers.Length && end < i
            ==> SubarraySum(numbers, start, end) <= result
    {
        var j := 0;
        while j <= i && i <= numbers.Length
            invariant 0 <= j <= i + 1
            invariant result >= 0
            invariant forall start: int, end: int :: 
                start <= end && 0 <= start && end <= numbers.Length && (end < i || (end == i && start < j))
                ==> SubarraySum(numbers, start, end) <= result
        {
            var currentSum := SubarraySum(numbers, j, i);
            if currentSum > result {
                result := currentSum;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

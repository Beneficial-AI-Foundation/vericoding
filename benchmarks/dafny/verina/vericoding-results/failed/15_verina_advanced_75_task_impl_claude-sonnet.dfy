// <vc-preamble>
function SpecSubarraySum(sequence: seq<int>, start: int, end: int): int
    decreases end - start
{
    if start >= end || start < 0 || end > |sequence| then
        0
    else if start + 1 == end then
        sequence[start]
    else
        sequence[start] + SpecSubarraySum(sequence, start + 1, end)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed lemma to establish subarray sum invariant */
lemma SpecSubarraySumCorrect(sequence: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |sequence|
    ensures SpecSubarraySum(sequence, start, end) == if start == end then 0 else sequence[start..end][0] + SpecSubarraySum(sequence, start + 1, end)
{
}

function SubarraySum(sequence: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |sequence|
    decreases end - start
{
    if start == end then 0 else sequence[start] + SubarraySum(sequence, start + 1, end)
}

lemma SubarraySumEqualsSpec(sequence: seq<int>, start: int, end: int)
    requires 0 <= start <= end <= |sequence|
    ensures SubarraySum(sequence, start, end) == SpecSubarraySum(sequence, start, end)
    decreases end - start
{
    if start >= end {
    } else if start + 1 == end {
    } else {
        SubarraySumEqualsSpec(sequence, start + 1, end);
    }
}

lemma SpecSubarraySumInductive(sequence: seq<int>, start: int, k: int)
    requires 0 <= start <= k <= |sequence|
    ensures SpecSubarraySum(sequence, start, k) + (if k < |sequence| then sequence[k] else 0) == 
            SpecSubarraySum(sequence, start, if k < |sequence| then k + 1 else k)
    decreases k - start
{
    if start == k {
    } else if start + 1 == k {
    } else {
        SpecSubarraySumInductive(sequence, start + 1, k);
    }
}

method ComputeSubarraySum(sequence: array<int>, start: int, end: int) returns (sum: int)
    requires 0 <= start <= end <= sequence.Length
    ensures sum == SpecSubarraySum(sequence[..], start, end)
{
    sum := 0;
    var k := start;
    while k < end
        invariant start <= k <= end
        invariant sum == SpecSubarraySum(sequence[..], start, k)
    {
        SpecSubarraySumInductive(sequence[..], start, k);
        sum := sum + sequence[k];
        k := k + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method TaskCode(sequence: array<int>) returns (result: int)
    requires sequence.Length > 0
    ensures 
        exists start: int, end: int :: 
            0 <= start < end <= sequence.Length && 
            result == SpecSubarraySum(sequence[..], start, end) &&
            forall s: int, e: int :: (0 <= s < e <= sequence.Length) ==> 
                SpecSubarraySum(sequence[..], s, e) <= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): simplified to avoid complex invariant violations */
{
    var maxSum := sequence[0];
    var maxStart := 0;
    var maxEnd := 1;
    
    var i := 0;
    while i < sequence.Length
        invariant 0 <= i <= sequence.Length
        invariant 0 <= maxStart < maxEnd <= sequence.Length
        invariant maxSum == SpecSubarraySum(sequence[..], maxStart, maxEnd)
    {
        var j := i + 1;
        while j <= sequence.Length
            invariant i < j <= sequence.Length
            invariant 0 <= maxStart < maxEnd <= sequence.Length
            invariant maxSum == SpecSubarraySum(sequence[..], maxStart, maxEnd)
        {
            var currentSum := ComputeSubarraySum(sequence, i, j);
            if currentSum > maxSum {
                maxSum := currentSum;
                maxStart := i;
                maxEnd := j;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := maxSum;
}
// </vc-code>

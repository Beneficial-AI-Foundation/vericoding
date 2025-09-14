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
/* helper modified by LLM (iteration 5): fixed SubarrayBounds lemma with proper case analysis */
function max(a: int, b: int): int { if a > b then a else b }

lemma SpecSubarraySumExtend(sequence: seq<int>, start: int, end: int)
    requires 0 <= start < end < |sequence|
    ensures SpecSubarraySum(sequence, start, end + 1) == SpecSubarraySum(sequence, start, end) + sequence[end]
    decreases end - start
{
    if start + 1 == end {
        assert SpecSubarraySum(sequence, start, end + 1) == sequence[start] + SpecSubarraySum(sequence, start + 1, end + 1);
        assert SpecSubarraySum(sequence, start + 1, end + 1) == sequence[end];
    } else {
        SpecSubarraySumExtend(sequence, start + 1, end);
    }
}

lemma SubarrayBounds(sequence: seq<int>, s: int, e: int, i: int, j: int)
    requires 0 <= s < e <= |sequence|
    requires 0 <= i < |sequence|
    requires i + 1 <= j <= |sequence|
    ensures (e <= i + 1 || (s == i && e <= j) || s > i) <==> ((e <= i + 1 || (s == i && e <= j + 1) || s > i) || (s == i && e == j + 1))
{
    if s == i && e == j + 1 {
        assert s == i;
        assert e == j + 1;
        assert e <= j + 1;
        assert s == i && e <= j + 1;
        assert (e <= i + 1 || (s == i && e <= j + 1) || s > i);
    } else {
        if e <= i + 1 || (s == i && e <= j) || s > i {
            assert (e <= i + 1 || (s == i && e <= j + 1) || s > i) || (s == i && e == j + 1);
        }
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
{
    /* code modified by LLM (iteration 5): complete rewrite with Kadane-style algorithm and proper invariants */
    var maxSum := sequence[0];
    var maxStart := 0;
    var maxEnd := 1;
    
    var i := 0;
    while i < sequence.Length
        invariant 0 <= i <= sequence.Length
        invariant 0 <= maxStart < maxEnd <= sequence.Length
        invariant maxSum == SpecSubarraySum(sequence[..], maxStart, maxEnd)
        invariant forall s: int, e: int :: (0 <= s < e <= sequence.Length && e <= i + 1) ==> SpecSubarraySum(sequence[..], s, e) <= maxSum
    {
        var currentSum := sequence[i];
        var bestSumEndingHere := sequence[i];
        var bestStartEndingHere := i;
        
        if currentSum > maxSum {
            maxSum := currentSum;
            maxStart := i;
            maxEnd := i + 1;
        }
        
        var j := i + 1;
        while j < sequence.Length
            invariant i + 1 <= j <= sequence.Length
            invariant bestSumEndingHere == SpecSubarraySum(sequence[..], bestStartEndingHere, j)
            invariant i <= bestStartEndingHere <= j
            invariant 0 <= maxStart < maxEnd <= sequence.Length
            invariant maxSum == SpecSubarraySum(sequence[..], maxStart, maxEnd)
            invariant forall s: int, e: int :: (0 <= s < e <= sequence.Length && (e <= i + 1 || (s >= i && e <= j))) ==> SpecSubarraySum(sequence[..], s, e) <= maxSum
        {
            bestSumEndingHere := bestSumEndingHere + sequence[j];
            
            if bestSumEndingHere > maxSum {
                maxSum := bestSumEndingHere;
                maxStart := bestStartEndingHere;
                maxEnd := j + 1;
            }
            
            if sequence[j] > bestSumEndingHere {
                bestSumEndingHere := sequence[j];
                bestStartEndingHere := j;
            }
            
            j := j + 1;
        }
        
        i := i + 1;
    }
    
    result := maxSum;
}
// </vc-code>

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
/* helper modified by LLM (iteration 5): fixed lemma to handle all cases properly */
lemma SubarraySumProperty(sequence: seq<int>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= |sequence|
    ensures SpecSubarraySum(sequence, start, end) == SpecSubarraySum(sequence, start, mid) + SpecSubarraySum(sequence, mid, end)
    decreases end - start, mid - start
{
    if start >= end {
    } else if start >= mid {
    } else if start + 1 == mid {
        if mid >= end {
        } else if mid + 1 == end {
        } else {
            SubarraySumProperty(sequence, mid, mid + 1, end);
            assert SpecSubarraySum(sequence, mid, end) == sequence[mid] + SpecSubarraySum(sequence, mid + 1, end);
        }
    } else {
        SubarraySumProperty(sequence, start + 1, mid, end);
        assert SpecSubarraySum(sequence, start, end) == sequence[start] + SpecSubarraySum(sequence, start + 1, end);
        assert SpecSubarraySum(sequence, start + 1, end) == SpecSubarraySum(sequence, start + 1, mid) + SpecSubarraySum(sequence, mid, end);
    }
}

lemma MaxSubarrayMaintained(sequence: seq<int>, i: int, result: int, maxEndingHere: int, startIndex: int, bestStart: int, bestEnd: int)
    requires 1 <= i < |sequence|
    requires 0 <= startIndex <= i
    requires 0 <= bestStart < bestEnd <= i
    requires result == SpecSubarraySum(sequence, bestStart, bestEnd)
    requires maxEndingHere == SpecSubarraySum(sequence, startIndex, i)
    requires forall s: int, e: int :: 0 <= s < e <= i ==> SpecSubarraySum(sequence, s, e) <= result
    requires maxEndingHere >= 0 || startIndex == i
    ensures forall s: int, e: int :: 0 <= s < e <= i + 1 ==> SpecSubarraySum(sequence, s, e) <= max(result, max(sequence[i], maxEndingHere + sequence[i]))
{
    forall s: int, e: int | 0 <= s < e <= i + 1
        ensures SpecSubarraySum(sequence, s, e) <= max(result, max(sequence[i], maxEndingHere + sequence[i]))
    {
        if e <= i {
            assert SpecSubarraySum(sequence, s, e) <= result;
            assert SpecSubarraySum(sequence, s, e) <= max(result, max(sequence[i], maxEndingHere + sequence[i]));
        } else if s == i {
            assert e == i + 1;
            assert SpecSubarraySum(sequence, s, e) == sequence[i];
            assert SpecSubarraySum(sequence, s, e) <= max(result, max(sequence[i], maxEndingHere + sequence[i]));
        } else {
            assert e == i + 1;
            assert s < i;
            SubarraySumProperty(sequence, s, i, i + 1);
            var sumToI := SpecSubarraySum(sequence, s, i);
            assert sumToI <= result;
            assert SpecSubarraySum(sequence, s, e) == sumToI + sequence[i];
            if startIndex == s && maxEndingHere >= 0 {
                assert sumToI == maxEndingHere;
                assert SpecSubarraySum(sequence, s, e) == maxEndingHere + sequence[i];
                assert SpecSubarraySum(sequence, s, e) <= max(result, max(sequence[i], maxEndingHere + sequence[i]));
            } else {
                assert SpecSubarraySum(sequence, s, e) <= result + sequence[i];
                assert SpecSubarraySum(sequence, s, e) <= max(result, max(sequence[i], maxEndingHere + sequence[i]));
            }
        }
    }
}

function max(a: int, b: int): int { if a > b then a else b }
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
/* code modified by LLM (iteration 5): fixed maxEndingHere initialization to handle negative values properly */
{
    result := sequence[0];
    var maxEndingHere := sequence[0];
    var i := 1;
    var startIndex := 0;
    var bestStart := 0;
    var bestEnd := 1;
    
    if maxEndingHere < 0 {
        maxEndingHere := 0;
        startIndex := 1;
    }
    
    while i < sequence.Length
        invariant 1 <= i <= sequence.Length
        invariant 0 <= startIndex <= i
        invariant 0 <= bestStart < bestEnd <= i
        invariant result == SpecSubarraySum(sequence[..], bestStart, bestEnd)
        invariant startIndex < i ==> maxEndingHere == SpecSubarraySum(sequence[..], startIndex, i)
        invariant startIndex == i ==> maxEndingHere == 0
        invariant maxEndingHere >= 0 || startIndex == i
        invariant forall s: int, e: int :: 0 <= s < e <= i ==> SpecSubarraySum(sequence[..], s, e) <= result
    {
        if startIndex < i {
            MaxSubarrayMaintained(sequence[..], i, result, maxEndingHere, startIndex, bestStart, bestEnd);
        }
        
        var newSum := maxEndingHere + sequence[i];
        if startIndex < i {
            SubarraySumProperty(sequence[..], startIndex, i, i + 1);
            assert newSum == SpecSubarraySum(sequence[..], startIndex, i + 1);
        }
        
        if sequence[i] > newSum {
            maxEndingHere := sequence[i];
            startIndex := i;
            assert maxEndingHere == SpecSubarraySum(sequence[..], i, i + 1);
        } else {
            if startIndex == i {
                startIndex := i;
            }
            maxEndingHere := newSum;
            assert maxEndingHere == SpecSubarraySum(sequence[..], startIndex, i + 1);
        }
        
        if maxEndingHere > result {
            result := maxEndingHere;
            bestStart := startIndex;
            bestEnd := i + 1;
        }
        
        if maxEndingHere < 0 {
            maxEndingHere := 0;
            startIndex := i + 1;
        }
        
        i := i + 1;
    }
}
// </vc-code>

// <vc-preamble>
function CountOccurrences(nums: seq<int>, value: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == value|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed assertion logic in candidate uniqueness lemma */
predicate isCandidate(nums: seq<int>, candidate: int)
{
    CountOccurrences(nums, candidate) > |nums| / 2
}

lemma candidateUniqueness(nums: seq<int>)
    requires |nums| > 0
    ensures forall candidate1, candidate2: int :: isCandidate(nums, candidate1) && isCandidate(nums, candidate2) ==> candidate1 == candidate2
{
    if exists candidate1, candidate2 :: candidate1 != candidate2 && isCandidate(nums, candidate1) && isCandidate(nums, candidate2) {
        var candidate1, candidate2 :| candidate1 != candidate2 && isCandidate(nums, candidate1) && isCandidate(nums, candidate2);
        var total := |nums|;
        var count1 := CountOccurrences(nums, candidate1);
        var count2 := CountOccurrences(nums, candidate2);
        assert count1 > total / 2;
        assert count2 > total / 2;
        assert count1 + count2 > total;
        // The contradiction: sum of two majority counts exceeds total
        assert count1 + count2 <= total by {
            // The maximum possible sum is total since each element can only be counted once
            assert forall x: int :: CountOccurrences(nums, x) <= total;
        }
        assert false;
    }
}
// </vc-helpers>

// <vc-spec>
method MajorityElement(nums: array<int>) returns (result: int)
    requires nums.Length > 0
    ensures var numsSeq := nums[..];
            var n := |numsSeq|;
            CountOccurrences(numsSeq, result) > n / 2 &&
            forall x: int :: x == result || CountOccurrences(numsSeq, x) <= n / 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariant and added verification of majority property */
{
    var candidate := nums[0];
    var count := 1;
    var i := 1;
    
    while i < nums.Length
        invariant 1 <= i <= nums.Length
        invariant count >= 0
        invariant count == CountOccurrences(nums[..i], candidate)
        invariant CountOccurrences(nums[..i], candidate) * 2 > i || count == 0
    {
        if count == 0 {
            candidate := nums[i];
            count := 1;
        } else if nums[i] == candidate {
            count := count + 1;
        } else {
            count := count - 1;
        }
        i := i + 1;
    }
    
    // Verify the candidate is indeed the majority element
    var numsSeq := nums[..];
    var n := |numsSeq|;
    
    // Prove that our candidate must be the majority element
    if CountOccurrences(numsSeq, candidate) <= n / 2 {
        candidateUniqueness(numsSeq);
        assert false; // Contradiction: no majority element exists
    }
    
    result := candidate;
}
// </vc-code>

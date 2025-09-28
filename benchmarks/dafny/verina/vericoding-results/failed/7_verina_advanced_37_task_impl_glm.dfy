// <vc-preamble>
function CountOccurrences(nums: seq<int>, value: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == value|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added disjointness assertion for sets */
lemma MajorityElementLemma(nums: seq<int>, candidate: int)
    requires |nums| > 0
    requires var counts := CountOccurrences(nums, candidate);
            counts > |nums| / 2
    ensures forall x: int :: x == candidate || CountOccurrences(nums, x) <= |nums| / 2
{
    forall x: int | x != candidate
        ensures CountOccurrences(nums, x) <= |nums| / 2
    {
        var totalCounts := |nums|;
        var candidateCounts := CountOccurrences(nums, candidate);
        var otherCounts := CountOccurrences(nums, x);
        
        assert disjoint({i | 0 <= i < |nums| && nums[i] == candidate}, {i | 0 <= i < |nums| && nums[i] == x});
        assert candidateCounts + otherCounts <= totalCounts;
        assert otherCounts <= totalCounts - candidateCounts;
        assert otherCounts <= totalCounts - (totalCounts / 2 + 1);
        assert otherCounts <= totalCounts / 2;
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
{
    var numsSeq := nums[..];
    var candidate := FindCandidate(numsSeq);
    
    var count := 0;
    var i := 0;
    while (i < |numsSeq|)
        invariant 0 <= i <= |numsSeq|
        invariant count == CountOccurrences(numsSeq[0..i], candidate)
    {
        if numsSeq[i] == candidate {
            count := count + 1;
        }
        i := i + 1;
    }
    
    result := candidate;
    MajorityElementLemma(numsSeq, result);
}
// </vc-code>

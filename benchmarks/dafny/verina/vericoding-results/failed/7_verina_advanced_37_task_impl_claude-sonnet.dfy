// <vc-preamble>
function CountOccurrences(nums: seq<int>, value: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == value|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma proofs with proper cardinality reasoning */
predicate IsMajority(nums: seq<int>, candidate: int)
{
    CountOccurrences(nums, candidate) > |nums| / 2
}

lemma CountCorrectness(nums: seq<int>, value: int, count: nat)
    requires count == CountOccurrences(nums, value)
    ensures count > |nums| / 2 <==> IsMajority(nums, value)
{
}

lemma MajorityUnique(nums: seq<int>, x: int, y: int)
    requires IsMajority(nums, x) && IsMajority(nums, y)
    ensures x == y
{
    if x != y {
        var xCount := CountOccurrences(nums, x);
        var yCount := CountOccurrences(nums, y);
        var s1 := set i | 0 <= i < |nums| && nums[i] == x;
        var s2 := set i | 0 <= i < |nums| && nums[i] == y;
        assert s1 !! s2;
        assert s1 + s2 <= set i | 0 <= i < |nums|;
        assert |s1 + s2| <= |nums|;
        assert |s1| + |s2| <= |nums|;
        assert xCount + yCount <= |nums|;
        assert false;
    }
}

lemma CountSliceInvariant(nums: seq<int>, value: int, j: int)
    requires 0 <= j <= |nums|
    ensures CountOccurrences(nums[..j], value) <= CountOccurrences(nums, value)
{
    var s1 := set i | 0 <= i < j && nums[i] == value;
    var s2 := set i | 0 <= i < |nums| && nums[i] == value;
    assert s1 <= s2;
}

lemma CountSliceExtend(nums: seq<int>, value: int, j: int)
    requires 0 <= j < |nums|
    ensures CountOccurrences(nums[..j+1], value) == 
            CountOccurrences(nums[..j], value) + (if nums[j] == value then 1 else 0)
{
    var s1 := set i | 0 <= i < j && nums[i] == value;
    var s2 := set i | 0 <= i < j+1 && nums[i] == value;
    if nums[j] == value {
        assert s2 == s1 + {j};
        assert j !in s1;
    } else {
        assert s2 == s1;
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
    /* code modified by LLM (iteration 5): simplified logic with proper post-loop handling */
    var numsSeq := nums[..];
    var n := nums.Length;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
    {
        var candidate := nums[i];
        var count := 0;
        var j := 0;
        
        while j < n
            invariant 0 <= j <= n
            invariant count == CountOccurrences(numsSeq[..j], candidate)
        {
            CountSliceInvariant(numsSeq, candidate, j);
            if nums[j] == candidate {
                count := count + 1;
            }
            CountSliceExtend(numsSeq, candidate, j);
            j := j + 1;
        }
        
        assert numsSeq[..n] == numsSeq;
        assert count == CountOccurrences(numsSeq, candidate);
        
        if count > n / 2 {
            result := candidate;
            CountCorrectness(numsSeq, candidate, count);
            assert IsMajority(numsSeq, candidate);
            
            forall x: int | x != candidate
                ensures CountOccurrences(numsSeq, x) <= n / 2
            {
                if CountOccurrences(numsSeq, x) > n / 2 {
                    MajorityUnique(numsSeq, candidate, x);
                }
            }
            return;
        }
        
        i := i + 1;
    }
    
    result := nums[0];
}
// </vc-code>

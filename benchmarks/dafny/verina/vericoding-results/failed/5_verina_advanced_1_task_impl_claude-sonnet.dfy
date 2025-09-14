// <vc-preamble>
// Helper function to count occurrences of an element in a sequence
function CountOccurrences(nums: seq<int>, x: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == x|
}

// Helper function to filter elements equal to x (recursive implementation)
function FilterEqual(nums: seq<int>, x: int): seq<int>
{
    if |nums| == 0 then []
    else if nums[0] == x then [nums[0]] + FilterEqual(nums[1..], x)
    else FilterEqual(nums[1..], x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma to use correct function signature */
lemma CountOccurrencesSliceProperty(nums: seq<int>, x: int, j: int)
    requires 0 <= j <= |nums|
    ensures CountOccurrences(nums[..j], x) <= CountOccurrences(nums[..], x)
{
    if j == |nums| {
        assert nums[..j] == nums[..];
    } else {
        var fullCount := |set i | 0 <= i < |nums| && nums[i] == x|;
        var sliceCount := |set i | 0 <= i < j && nums[i] == x|;
        assert sliceCount <= fullCount;
    }
}

lemma SliceInvariantHelper(nums: seq<int>, i: int, j: int)
    requires 0 <= i < |nums|
    requires 0 <= j <= |nums|
    ensures CountOccurrences(nums[..j], nums[i]) == |set k | 0 <= k < j && nums[k] == nums[i]|
{
    assert CountOccurrences(nums[..j], nums[i]) == |set k | 0 <= k < |nums[..j]| && nums[..j][k] == nums[i]|;
    assert |set k | 0 <= k < |nums[..j]| && nums[..j][k] == nums[i]| == |set k | 0 <= k < j && nums[k] == nums[i]|;
}

lemma UniqueElementExists(nums: seq<int>)
    requires exists unique_elem :: CountOccurrences(nums, unique_elem) == 1
    requires forall elem :: elem in nums ==> (CountOccurrences(nums, elem) == 1 || CountOccurrences(nums, elem) == 2)
    ensures exists x :: x in nums && CountOccurrences(nums, x) == 1
{
    var unique_elem :| CountOccurrences(nums, unique_elem) == 1;
    assert unique_elem in nums;
}
// </vc-helpers>

// <vc-spec>
method FindSingleNumber(nums: array<int>) returns (result: int)
    requires 
        nums.Length > 0
    requires
        exists unique_elem :: CountOccurrences(nums[..], unique_elem) == 1
    requires
        forall elem :: elem in nums[..] ==> (CountOccurrences(nums[..], elem) == 1 || CountOccurrences(nums[..], elem) == 2)
    ensures
        CountOccurrences(nums[..], result) == 1
    ensures
        forall x :: x in nums[..] ==> (x == result || CountOccurrences(nums[..], x) == 2)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): simplified implementation with proper initialization and invariant handling */
{
    result := nums[0];
    var found := false;
    
    for i := 0 to nums.Length
        invariant 0 <= i <= nums.Length
        invariant found ==> (result in nums[..] && CountOccurrences(nums[..], result) == 1)
        invariant !found ==> forall x :: x in nums[..i] ==> CountOccurrences(nums[..], x) != 1
        invariant found ==> (forall x :: x in nums[..i] && CountOccurrences(nums[..], x) == 1 ==> x == result)
    {
        var count := 0;
        for j := 0 to nums.Length
            invariant 0 <= j <= nums.Length
            invariant count == |set k | 0 <= k < j && nums[k] == nums[i]|
        {
            if nums[j] == nums[i] {
                count := count + 1;
            }
        }
        
        if count == 1 {
            result := nums[i];
            found := true;
        }
    }
}
// </vc-code>

// IMPL 
method contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
{
    var i := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        /* code modified by LLM (iteration 1): strengthened invariant to maintain that all pairs up to i are distinct */
        invariant forall x, y :: 0 <= x < y < i ==> nums[x] != nums[y]
    {
        var j := i + 1;
        while j < |nums|
            invariant i < j <= |nums|
            invariant forall x, y :: 0 <= x < y < i ==> nums[x] != nums[y]
            /* code modified by LLM (iteration 1): invariant to track that nums[i] is different from all checked elements after i */
            invariant forall k :: i + 1 <= k < j ==> nums[i] != nums[k]
        {
            if nums[i] == nums[j] {
                /* code modified by LLM (iteration 1): return false since sequence is not distinct when duplicate found */
                result := false;
                return;
            }
            j := j + 1;
        }
        /* code modified by LLM (iteration 1): assert that nums[i] is different from all elements after i */
        assert forall k :: i + 1 <= k < |nums| ==> nums[i] != nums[k];
        i := i + 1;
    }
    /* code modified by LLM (iteration 1): assert and return true since all pairs are distinct */
    assert forall x, y :: 0 <= x < y < |nums| ==> nums[x] != nums[y];
    result := true;
}

// ATOM 

predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}
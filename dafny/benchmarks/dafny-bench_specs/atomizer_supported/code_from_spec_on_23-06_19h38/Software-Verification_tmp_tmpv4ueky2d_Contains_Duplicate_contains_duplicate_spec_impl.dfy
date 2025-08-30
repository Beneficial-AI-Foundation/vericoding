//IMPL 
/* code modified by LLM (iteration 1): Fixed method logic to match postcondition, simplified and corrected loop invariants */
method contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
{
    var seen := {};
    var i := 0;
    
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant seen == set k | 0 <= k < i :: nums[k]
        invariant forall k, j :: 0 <= k < j < i ==> nums[k] != nums[j]
    {
        if nums[i] in seen {
            /* code modified by LLM (iteration 1): Changed return value to false since we found a duplicate, meaning sequence is not distinct */
            result := false;
            return;
        }
        seen := seen + {nums[i]};
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): Return true since no duplicates found, meaning sequence is distinct */
    result := true;
}

//ATOM 
predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}
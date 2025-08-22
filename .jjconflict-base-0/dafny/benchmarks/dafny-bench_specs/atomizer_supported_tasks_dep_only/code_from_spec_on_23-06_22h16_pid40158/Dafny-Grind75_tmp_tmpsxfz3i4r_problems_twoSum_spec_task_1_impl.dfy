// ATOM 
predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}

//IMPL twoSum
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{
    var i := 0;
    while i < |nums|
        /* code modified by LLM (iteration 1): Fixed outer loop invariant to properly track searched pairs */
        invariant 0 <= i <= |nums|
        invariant forall x: nat, y: nat :: x < y < |nums| && x < i && summingPair(x, y, nums, target) ==> false
    {
        var j := i + 1;
        while j < |nums|
            /* code modified by LLM (iteration 1): Fixed inner loop invariant to properly track current row search */
            invariant i < j <= |nums|
            invariant forall y: nat :: i < y < j && summingPair(i, y, nums, target) ==> false
        {
            if nums[i] + nums[j] == target {
                /* code modified by LLM (iteration 1): Added assertion to help prove postcondition */
                assert summingPair(i, j, nums, target);
                pair := (i, j);
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): Added unreachable code marker since precondition guarantees a solution exists */
    assert false; // This should be unreachable given the precondition
}
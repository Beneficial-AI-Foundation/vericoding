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
        /* code modified by LLM (iteration 1): strengthened invariant to track all checked pairs */
        invariant 0 <= i <= |nums|
        invariant forall x: nat, y: nat :: x < |nums| && y < |nums| && x < y && y < i ==> !summingPair(x, y, nums, target)
        invariant forall x: nat, y: nat :: x < |nums| && y < |nums| && x < i && y > x ==> !summingPair(x, y, nums, target)
    {
        var j := i + 1;
        while j < |nums|
            /* code modified by LLM (iteration 1): fixed invariant bounds and added preservation */
            invariant i + 1 <= j <= |nums|
            invariant i < |nums|
            invariant forall y: nat :: y < |nums| && i < y < j ==> !summingPair(i, y, nums, target)
        {
            /* code modified by LLM (iteration 1): added assertion to help prove postcondition */
            if nums[i] + nums[j] == target {
                assert i < j;
                assert summingPair(i, j, nums, target);
                pair := (i, j);
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 1): added unreachable code to satisfy postcondition */
    // This should never be reached due to the precondition
    assert false;
    pair := (0, 0);
}
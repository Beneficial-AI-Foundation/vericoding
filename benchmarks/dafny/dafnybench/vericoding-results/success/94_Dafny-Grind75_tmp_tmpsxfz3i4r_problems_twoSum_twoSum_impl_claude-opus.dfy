predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant forall i': nat, j': nat :: i' < i && i' < j' < |nums| ==> !summingPair(i', j', nums, target)
    {
        var j := i + 1;
        while j < |nums|
            invariant i + 1 <= j <= |nums|
            invariant forall j': nat :: i < j' < j ==> !summingPair(i, j', nums, target)
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    // This point should be unreachable due to the precondition
    assert false;
}
// </vc-code>


predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}

// <vc-helpers>
predicate distinctPair(l: nat, m: nat, i: nat, j: nat)
{
    (l != i || m != j) && (l != j || m != i)
}
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
        invariant forall l: nat, m: nat :: l < m < |nums| && l < i ==> !summingPair(l, m, nums, target)
    {
        var j := i + 1;
        while j < |nums|
            invariant i < j <= |nums|
            invariant forall l: nat, m: nat :: l < m < |nums| && (l < i || (l == i && m < j)) ==> !summingPair(l, m, nums, target)
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    // This line should be unreachable given the precondition
    // We add a default return to satisfy Dafny's termination requirements,
    // though the precondition guarantees a pair will be found.
    assert false; // This line should be unreachable
    return (0, 1);
}
// </vc-code>


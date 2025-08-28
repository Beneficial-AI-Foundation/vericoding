predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}

// <vc-helpers>
lemma PairExists(nums: seq<int>, target: int)
    requires exists i:nat, j:nat :: i < j < |nums| && summingPair(i, j, nums, target)
    ensures exists i:nat, j:nat :: i < j < |nums| && summingPair(i, j, nums, target)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
// </vc-spec>
// </vc-spec>

// <vc-code>
method TwoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l < m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{
    var i: nat := 0;
    var found := false;
    pair := (0, 1);
    
    while i < |nums| && !found
        decreases |nums| - i
    {
        var j: nat := i + 1;
        while j < |nums| && !found
            decreases |nums| - j
        {
            if nums[i] + nums[j] == target {
                pair := (i, j);
                found := true;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

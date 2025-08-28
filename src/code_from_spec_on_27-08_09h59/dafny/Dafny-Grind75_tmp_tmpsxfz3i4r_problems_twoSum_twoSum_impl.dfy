predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}

// <vc-helpers>
lemma uniquePairExists(nums: seq<int>, target: int) returns (i: nat, j: nat)
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures i < j < |nums| && summingPair(i, j, nums, target)
{
    var witness_i: nat :| witness_i >= 0 && exists j:nat :: witness_i < j < |nums| && summingPair(witness_i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != witness_i && m != j ==> !summingPair(l, m, nums, target);
    var witness_j: nat :| witness_j >= 0 && witness_i < witness_j < |nums| && summingPair(witness_i, witness_j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != witness_i && m != witness_j ==> !summingPair(l, m, nums, target);
    return witness_i, witness_j;
}

method findPair(nums: seq<int>, target: int) returns (i: nat, j: nat)
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures i < j < |nums| && summingPair(i, j, nums, target)
{
    var witness_i: nat :| witness_i >= 0 && exists j:nat :: witness_i < j < |nums| && summingPair(witness_i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != witness_i && m != j ==> !summingPair(l, m, nums, target);
    var witness_j: nat :| witness_j >= 0 && witness_i < witness_j < |nums| && summingPair(witness_i, witness_j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != witness_i && m != witness_j ==> !summingPair(l, m, nums, target);
    return witness_i, witness_j;
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
{
    var i, j := findPair(nums, target);
    return (i, j);
}
// </vc-code>

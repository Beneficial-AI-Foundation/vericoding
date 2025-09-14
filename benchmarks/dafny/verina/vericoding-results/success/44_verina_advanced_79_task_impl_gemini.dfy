// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
predicate FoundNoSolutionBefore(nums: array<int>, target: int, i_limit: nat, j_limit: nat)
    reads nums
{
    forall k1: nat, k2: nat :: k1 < k2 < nums.Length && (k1 < i_limit || (k1 == i_limit && k2 < j_limit)) ==> nums[k1] + nums[k2] != target
}
// </vc-helpers>

// <vc-spec>
method TwoSum(nums: array<int>, target: int) returns (result: Option<(nat, nat)>)
    ensures
        match result {
            case None => 
                forall i: int, j: int :: 0 <= i < nums.Length && 0 <= j < nums.Length && i != j ==> nums[i] + nums[j] != target
            case Some((i, j)) => 
                i < j &&
                j < nums.Length &&
                nums[i] + nums[j] == target &&
                forall k1: int, k2: int :: 0 <= k1 < nums.Length && 0 <= k2 < nums.Length && k1 < k2 && (k1 < i || (k1 == i && k2 < j)) ==> nums[k1] + nums[k2] != target
        }
// </vc-spec>
// <vc-code>
{
    var i: nat := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant FoundNoSolutionBefore(nums, target, i, 0)
    {
        var j: nat := i + 1;
        while j < nums.Length
            invariant i < nums.Length
            invariant i < j <= nums.Length
            invariant FoundNoSolutionBefore(nums, target, i, j)
        {
            if nums.Length > 0 && i < nums.Length && j < nums.Length && nums[i] + nums[j] == target {
                result := Some((i, j));
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    result := None;
}
// </vc-code>

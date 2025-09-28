// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
// No helpers needed for this problem.
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
        invariant forall k1: int, k2: int :: 0 <= k1 < i && 0 <= k2 < nums.Length && k1 < k2 ==> nums[k1] + nums[k2] != target
    {
        var j: nat := (i + 1) as nat;
        while j < nums.Length
            invariant i < j <= nums.Length
            invariant forall k2: int :: i < k2 < j ==> nums[i] + nums[k2] != target
            invariant forall k1: int, k2: int :: 0 <= k1 < i && 0 <= k2 < nums.Length && k1 < k2 ==> nums[k1] + nums[k2] != target
        {
            if nums[i] + nums[j] == target {
                return Some((i, j));
            }
            j := j + 1;
        }
        i := i + 1;
    }
    return None;
}
// </vc-code>

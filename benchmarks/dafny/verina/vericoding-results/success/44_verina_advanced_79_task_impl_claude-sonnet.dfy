// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
predicate ValidIndices(i: nat, j: nat, len: nat)
{
    i < len && j < len && i != j
}

function MinPair(i1: nat, j1: nat, i2: nat, j2: nat): (nat, nat)
{
    if i1 < i2 || (i1 == i2 && j1 < j2) then (i1, j1) else (i2, j2)
}

predicate IsFirstValidPair(nums: array<int>, target: int, i: nat, j: nat)
    reads nums
{
    i < j &&
    j < nums.Length &&
    nums[i] + nums[j] == target &&
    forall k1: int, k2: int :: 0 <= k1 < nums.Length && 0 <= k2 < nums.Length && k1 < k2 && (k1 < i || (k1 == i && k2 < j)) ==> nums[k1] + nums[k2] != target
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
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall i1: int, j1: int :: 0 <= i1 < i && 0 <= j1 < nums.Length && i1 < j1 ==> nums[i1] + nums[j1] != target
    {
        var j := i + 1;
        while j < nums.Length
            invariant i + 1 <= j <= nums.Length
            invariant forall j1: int :: i + 1 <= j1 < j ==> nums[i] + nums[j1] != target
            invariant forall i1: int, j1: int :: 0 <= i1 < i && 0 <= j1 < nums.Length && i1 < j1 ==> nums[i1] + nums[j1] != target
        {
            if nums[i] + nums[j] == target {
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

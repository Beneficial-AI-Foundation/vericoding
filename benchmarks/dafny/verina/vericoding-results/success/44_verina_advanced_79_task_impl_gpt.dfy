// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>

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
  var n := nums.Length;
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k1:int, k2:int :: 0 <= k1 < n && 0 <= k2 < n && k1 < k2 && k1 < i ==> nums[k1] + nums[k2] != target
    decreases n - i
  {
    var j: nat := i + 1;
    while j < n
      invariant i < j <= n
      invariant forall k2:int :: i < k2 < j ==> nums[i] + nums[k2] != target
      invariant forall k1:int, k2:int :: 0 <= k1 < n && 0 <= k2 < n && k1 < k2 && k1 < i ==> nums[k1] + nums[k2] != target
      decreases n - j
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

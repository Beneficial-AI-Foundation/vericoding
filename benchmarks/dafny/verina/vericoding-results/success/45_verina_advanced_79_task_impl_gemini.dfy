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
  /* code modified by LLM (iteration 2): [fixed compilation error, used match in invariant, and strengthened invariant] */
  var i := 0;
  result := None;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant match result {
      case None => 
        forall k1, k2 :: 0 <= k1 < i && k1 < k2 < nums.Length ==> nums[k1] + nums[k2] != target
      case Some((r1, r2)) => 
        r1 < i &&
        r1 < r2 < nums.Length &&
        nums[r1] + nums[r2] == target &&
        forall k1, k2 :: 0 <= k1 < nums.Length && 0 <= k2 < nums.Length && k1 < k2 && (k1 < r1 || (k1 == r1 && k2 < r2)) ==> nums[k1] + nums[k2] != target
    }
  {
    if result.Some? { 
      break; 
    }
    var j := i + 1;
    while j < nums.Length
      invariant 0 <= i < nums.Length
      invariant i + 1 <= j <= nums.Length
      invariant forall k1, k2 :: (0 <= k1 < i && k1 < k2 < nums.Length) || (k1 == i && i < k2 < j) ==> nums[k1] + nums[k2] != target
      invariant result.None?
    {
      if nums[i] + nums[j] == target {
        result := Some((i as nat, j as nat));
        break; 
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

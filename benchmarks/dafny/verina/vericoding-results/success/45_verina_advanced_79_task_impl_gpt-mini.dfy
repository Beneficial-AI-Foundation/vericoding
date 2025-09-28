// <vc-preamble>
datatype Option<T> = None | Some(value: T)
// </vc-preamble>

// <vc-helpers>
{
  lemma IndexBounds(n: int, i: int)
    requires 0 <= i < n
    ensures 0 <= i && i < n
  {
  }
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
  var n := nums.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k1,k2 :: 0 <= k1 < n && 0 <= k2 < n && k1 < k2 && k1 < i ==> nums[k1] + nums[k2] != target
  {
    var j := i + 1;
    while j < n
      invariant 0 <= i < n
      invariant i + 1 <= j <= n
      invariant forall k1,k2 :: 0 <= k1 < n && 0 <= k2 < n && k1 < k2 && (k1 < i || (k1 == i && k2 < j)) ==> nums[k1] + nums[k2] != target
    {
      if nums[i] + nums[j] == target {
        result := Some((i as nat, j as nat));
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := None;
}

// </vc-code>

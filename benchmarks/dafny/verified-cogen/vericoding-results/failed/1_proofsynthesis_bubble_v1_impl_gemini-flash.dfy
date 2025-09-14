// <vc-preamble>
predicate SortedBetween(a: seq<int>, from: int, to: int)
    requires 0 <= from <= to <= |a|
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

predicate IsReorderOf<T(==)>(r: seq<int>, p: seq<T>, s: seq<T>)
    requires |r| == |p| && |r| == |s|
{
    && |r| == |s|
    && (forall i :: 0 <= i < |r| ==> 0 <= r[i] < |s|)
    && (forall i, j :: 0 <= i < j < |r| ==> r[i] != r[j])
    && (forall i :: 0 <= i < |r| ==> p[i] == s[r[i]])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Test1(nums: array<int>)
    modifies nums
    ensures SortedBetween(nums[..], 0, nums.Length)
    ensures exists r :: |r| == nums.Length && IsReorderOf(r, nums[..], old(nums[..]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors in `set` comprehension and refined invariants */
{
  var n := nums.Length;
  if n == 0 { return; }

  var old_nums := nums[..];

  for i := 0 to n - 2
    invariant 0 <= i < n
    invariant SortedBetween(nums[..], 0, i)
    invariant
      exists r ::
        |r| == n &&
        IsReorderOf(r, nums[..], old_nums) &&
        (forall k :: i <= k < n ==> r[k] in set (set x | 0 <= x < n)) // Corrected set comprehension syntax

  {
    var min_val := nums[i];
    var min_idx := i;
    for j := i + 1 to n - 1
      invariant i < j <= n
      invariant nums[min_idx] == min_val
      invariant i <= min_idx < j
      invariant forall k_smaller :: i <= k_smaller < j ==> nums[min_idx] <= nums[k_smaller]
      invariant SortedBetween(nums[..], 0, i)
      invariant exists r_inner :: |r_inner| == n && IsReorderOf(r_inner, nums[..], old_nums)

    {
      if nums[j] < min_val {
        min_val := nums[j];
        min_idx := j;
      }
    }
    if min_idx != i {
      var temp := nums[i];
      nums[i] := nums[min_idx];
      nums[min_idx] := temp;
    }
  }
}
// </vc-code>

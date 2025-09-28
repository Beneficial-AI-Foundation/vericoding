// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause */
function CompareElements(a: array<int>, i: int, j: int): int
    requires 0 <= i < a.Length && 0 <= j < a.Length
    reads a
    ensures CompareElements(a, i, j) == i || CompareElements(a, i, j) == j
    ensures a[CompareElements(a, i, j)] >= a[i] && a[CompareElements(a, i, j)] >= a[j]
{
    if a[i] >= a[j] then i else j
}
// </vc-helpers>

// <vc-spec>
method MaxArray(nums: array<int>) returns (idx: int)
    requires
        nums.Length >= 1
    ensures
        0 <= idx && idx < nums.Length &&
        forall i :: 0 <= i && i < nums.Length ==> nums[i] <= nums[idx]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): no changes needed */
  idx := 0;
  var i := 1;
  while i < nums.Length
      invariant 0 <= idx < nums.Length && 0 <= i <= nums.Length
      invariant forall j :: 0 <= j && j < i ==> nums[j] <= nums[idx]
  {
      if nums[i] > nums[idx] {
          idx := i;
      }
      i := i + 1;
  }
}
// </vc-code>

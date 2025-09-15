// <vc-preamble>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed helper to handle sorted array constraints and termination */
function count_sorted_helper(a: seq<int>, x: int, low: int, high: int): int
  requires 0 <= low <= high <= |a|
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  ensures count_sorted_helper(a, x, low, high) == |set i | low <= i < high && a[i] == x|
  decreases high - low
{
  if low >= high then
    0
  else if a[low] > x then
    0  // Since array is sorted, no more x's beyond this point
  else if a[low] < x then
    count_sorted_helper(a, x, low + 1, high)
  else
    1 + count_sorted_helper(a, x, low + 1, high)
}
// </vc-helpers>

// <vc-spec>
method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)

  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x

  ensures count == count_set(a, x)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Optimized search with binary bounds */
{
  var left_bound := pos;
  var right_bound := pos;
  
  // Find left boundary of x's
  while left_bound > 0 && a[left_bound - 1] == x
    decreases left_bound
    invariant 0 <= left_bound <= pos
    invariant a[left_bound] == x
    invariant forall i :: left_bound <= i <= pos ==> a[i] == x
  {
    left_bound := left_bound - 1;
  }
  
  // Find right boundary of x's  
  while right_bound < |a| - 1 && a[right_bound + 1] == x
    decreases |a| - right_bound
    invariant pos <= right_bound < |a|
    invariant a[right_bound] == x
    invariant forall i :: pos <= i <= right_bound ==> a[i] == x
  {
    right_bound := right_bound + 1;
  }
  
  count := right_bound - left_bound + 1;
}
// </vc-code>

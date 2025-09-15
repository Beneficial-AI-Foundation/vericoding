// <vc-preamble>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): fixed loop invariants and postcondition by ensuring the correct range for `low` and `high` and proving the postcondition. */
{
  var low := pos;
  var high := pos;

  // Find the leftmost occurrence of x
  while low > 0 && a[low - 1] == x
    invariant 0 <= low <= pos
    invariant forall k :: low <= k <= pos ==> a[k] == x
  {
    low := low - 1;
  }

  // Find the rightmost occurrence of x
  while high < |a| - 1 && a[high + 1] == x
    invariant pos <= high < |a|
    invariant forall k :: pos <= k <= high ==> a[k] == x
  {
    high := high + 1;
  }

  count := high - low + 1;

  // Proof for the ensures clause
  // We need to show that for any i, a[i] == x if and only if low <= i <= high.

  // ==> part: If a[i] == x, then low <= i <= high.
  // Case 1: i < low.
  // If low == 0, then this case is not possible. If low > 0, then by loop invariant and condition,
  // a[low-1] < x or a[low-1] != x for this specific iteration. Since the array is sorted and a[low] == x,
  // it must be that a[low-1] < x. Therefore, any i < low must have a[i] < x.
  assert forall i :: i < low ==> a[i] < x;

  // Case 2: i > high.
  // If high == |a|-1, then this case is not possible. If high < |a|-1, then by loop invariant and condition,
  // a[high+1] > x or a[high+1] != x for this specific iteration. Since the array is sorted and a[high] == x,
  // it must be that a[high+1] > x. Therefore, any i > high must have a[i] > x.
  assert forall i :: i > high ==> a[i] > x;

  // Combining Case 1 and Case 2:
  assert forall i :: 0 <= i < |a| && a[i] == x ==> low <= i <= high;

  // <== part: If low <= i <= high, then a[i] == x.
  // We know a[low] == x (from initial pos and first loop invariant).
  // We know a[high] == x (from initial pos and second loop invariant).
  // From the loop invariant of the first loop: forall k :: low <= k <= pos ==> a[k] == x.
  // From the loop invariant of the second loop: forall k :: pos <= k <= high ==> a[k] == x.
  // Therefore, forall k :: low <= k <= high ==> a[k] == x.
  assert forall i :: low <= i <= high ==> a[i] == x;

  assert count == count_set(a, x);
}
// </vc-code>

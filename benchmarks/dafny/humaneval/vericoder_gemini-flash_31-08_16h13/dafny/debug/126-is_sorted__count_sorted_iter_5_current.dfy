method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function count_set_helper(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// This helper function is correct and does not need changes.
// </vc-helpers>

// <vc-spec>
method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)
  // pre-conditions-start
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  // pre-conditions-end
  // post-conditions-start
  ensures count == count_set(a, x)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var current_count := 0;
  var i := pos;

  while i < |a| && a[i] == x
    invariant 0 <= pos <= i <= |a|
    invariant current_count == i - pos
    invariant forall k :: pos <= k < i ==> a[k] == x
    invariant forall k :: 0 <= k < pos ==> a[k] < x // From pre-condition pos == 0 || a[pos-1] < x and sortedness
    decreases |a| - i
  {
    current_count := current_count + 1;
    i := i + 1;
  }

  // At this point, i is the first index where a[i] != x or i == |a|.
  // So, all elements from pos to i-1 are equal to x.

  // Proof that count_set(a,x) is a subset of {k | pos <= k < i && a[k] == x} U {k | 0 <= k < pos && a[k] == x} U {k | i <= k < |a| && a[k] == x}

  // Part 1: Elements from pos to i-1 are 'x' and included in current_count
  // This is guaranteed by the loop invariant: forall k :: pos <= k < i ==> a[k] == x

  // Part 2: Elements before 'pos' are not 'x' (due to sortedness and pre-conditions)
  // We know: pos == 0 || a[pos - 1] < x
  // And a is sorted: forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  // Combining these, if k < pos, then a[k] <= a[pos-1]. If pos == 0, there are no such k.
  // If pos > 0, then a[pos-1] < x. Thus, a[k] < x for k < pos.
  assert (forall k :: 0 <= k < pos ==> a[k] < x);

  // Part 3: Elements from 'i' to |a|-1 are not 'x' (due to loop termination and sortedness)
  if i < |a| {
    // Loop terminated because a[i] != x
    assert a[i] != x;
    // Since a[i-1] == x (from loop invariant), and 'a' is sorted, a[i] must be >= a[i-1].
    // Given a[i] != x, it must be that a[i] > x.
    assert a[i] > x;
    // Because 'a' is sorted, for any k such that i <= k < |a|, we have a[k] >= a[i].
    // Since a[i] > x, it follows that a[k] > x for all such k.
    assert (forall k :: i <= k < |a| ==> a[k] > x);
  } else {
    // i == |a|, meaning there are no elements from i to |a|-1.
  }

  // Combining the parts:
  // An element a[k] equals x if and only if its index k is in the range [pos, i-1].
  assert (forall k :: 0 <= k < |a| && a[k] == x <==> pos <= k < i);

  // From the loop invariant, current_count equals i - pos.
  assert current_count == i - pos;

  // By definition of count_set, count_set(a, x) is the count of elements a[k] == x.
  // Based on the combined assertion above, these are exactly the elements in range [pos, i-1].
  assert count_set(a, x) == |set k | pos <= k < i && a[k] == x|;
  assert count_set(a, x) == i - pos;

  // Therefore, current_count is equal to count_set(a, x).
  assert current_count == count_set(a, x);

  return current_count;
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end
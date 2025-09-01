method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
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
  var count := 0;
  var i := pos;

  while i < |a| && a[i] == x
    invariant 0 <= pos <= i <= |a|
    invariant count == i - pos
    invariant forall k :: pos <= k < i ==> a[k] == x
    invariant forall k :: 0 <= k < pos ==> a[k] < x // From pre-condition pos == 0 || a[pos-1] < x and sortedness
    decreases |a| - i
  {
    count := count + 1;
    i := i + 1;
  }

  // At this point, i is the first index where a[i] != x or i == |a|.
  // So, all elements from pos to i-1 are equal to x.
  // We need to prove count == count_set(a, x).

  // Proof that count_set(a,x) is a subset of {k | pos <= k < i && a[k] == x} U {k | 0 <= k < pos && a[k] == x} U {k | i <= k < |a| && a[k] == x}

  // Part 1: Elements from pos to i-1 are 'x' and included in count
  // We already have: forall k :: pos <= k < i ==> a[k] == x

  // Part 2: Elements before 'pos' are not 'x' (due to sortedness and pre-conditions)
  assert forall k :: 0 <= k < pos ==> a[k] < x; // This comes from sorted pre-condition a[pos-1] < x or pos == 0
  assert (forall k :: 0 <= k < pos ==> a[k] != x);

  // Part 3: Elements from 'i' to |a|-1 are not 'x' (due to loop termination and sortedness)
  assert (i == |a| || a[i] != x);
  if i < |a| {
      assert a[i] != x;
      // Since 'a' is sorted, if a[i] != x and a[i] is defined, then a[i] must be > x
      // (a[i] cannot be < x because a[i-1] == x and a is sorted).
      assert a[i] > x;
      assert (forall k :: i <= k < |a| ==> a[k] > x); // Due to sortedness
      assert (forall k :: i <= k < |a| ==> a[k] != x);
  } else {
      // i == |a|, no elements after i.
  }

  // Combining the parts:
  // All elements equal to 'x' must be in the range [pos, i-1].
  assert (forall k :: 0 <= k < |a| && a[k] == x <==> pos <= k < i);
  // Therefore, count_set(a, x) and count (which is i - pos) are equal.
  assert count == i - pos;
  assert count_set(a, x) == i - pos;

  return count;
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end
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
{
  /* code modified by LLM (iteration 5): fixed typos (0.tome to 0, dbo to a[k]), corrected set comprehension syntax, ensured invariants align with ensures */
  count := 0;
  var i := pos;
  if pos > 0 {
    assert forall k :: 0 <= k < pos ==> a[k] != x;
  }
  while i < |a| && a[i] == x
    invariant i >= pos && i <= |a|
    invariant count == |set k | pos <= k < i && a[k] == x |
    invariant forall k :: 0 <= k < pos ==> a[k] != x
    decreases |a| - i
  {
    count := count + 1;
    i := i + 1;
  }
  if i < |a| {
    assert a[i] > x;
  }
  if i < |a| {
    assert forall k :: i <= k < |a| ==> a[k] != x;
  } else {
    assert |a| == i;
  }
  assert count == |set k | 0 <= k < |a| && a[k] == x |;
}
// </vc-code>

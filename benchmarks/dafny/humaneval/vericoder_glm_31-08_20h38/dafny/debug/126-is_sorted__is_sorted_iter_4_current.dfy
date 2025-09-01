

// <vc-helpers>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}

lemma distinct_indices_helper(a: seq<int>, x: int, i: int, j: int)
  requires 0 <= i < j < |a|
  requires a[i] == x
  requires a[j] == x
  requires forall k :: i < k < j ==> a[k] != x
  ensures count_set(a, x) >= 2
{
  calc {
    count_set(a, x);
    |set k | 0 <= k < |a| && a[k] == x|;
    >= |{i, j}|;
    2
  }
}
// </vc-helpers>

// <vc-spec>
method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var left := pos;
  var right := pos;
  
  // Extend left
  while left > 0 && a[left - 1] == x
    invariant 0 <= left <= pos
    invariant a[left] == x
    invariant forall i :: left <= i <= pos ==> a[i] == x
  {
    left := left - 1;
  }
  
  // Extend right
  while right < |a| - 1 && a[right + 1] == x
    invariant pos <= right < |a|
    invariant a[right] == x
    invariant forall i :: pos <= i <= right ==> a[i] == x
  {
    right := right + 1;
  }
  
  count := right - left + 1;
  
  // Prove correctness
  if left > 0 {
    assert a[left - 1] < x;
  }
  if right < |a| - 1 {
    assert a[right + 1] > x;
  }
  
  // All occurrences of x are between left and right
  assert forall i :: 0 <= i < left ==> a[i] < x;
  assert forall i :: right < i < |a| ==> a[i] > x;
  assert forall i :: left <= i <= right ==> a[i] == x;
  
  // Therefore, the count is correct
  assert count == count_set(a, x);
}
// </vc-code>

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
{
  assume{:axiom} false;
}
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end
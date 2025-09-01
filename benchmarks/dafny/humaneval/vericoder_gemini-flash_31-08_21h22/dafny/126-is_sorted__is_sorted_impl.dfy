

// <vc-helpers>
function is_sorted_and_at_most_two(a: seq<int>): bool
  reads a
{
  (forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]) && (forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2)
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
  if |a| <= 1 then
    return true;

  var sorted := true;
  var counts_ok := true;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant sorted == (forall k, l :: 0 <= k <= l < i ==> a[k] <= a[l])
    invariant counts_ok == (forall k :: 0 <= k < i ==> |set j | 0 <= j < i && a[j] == a[k]| <= 2)
    decreases |a| - i
  {
    if i > 0 && a[i-1] > a[i] then
      sorted := false;

    if count_set(a, a[i]) > 2 then
      counts_ok := false;
    i := i + 1;
  }
  return sorted && counts_ok;
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


// <vc-helpers>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
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
  var sorted := true;
  var i := 0;
  while i < |a| - 1
    decreases |a| -1 - i
    invariant 0 <= i <= |a|-1
    invariant sorted == (forall k :: 0 <= k < i ==> a[k] <= a[k + 1])
  {
    if a[i] > a[i + 1] { sorted := false; }
    i := i + 1;
  }
  var ok := true;
  i := 0;
  while i < |a|
    decreases |a| - i
    invariant 0 <= i <= |a|
    invariant ok == (forall k :: 0 <= k < i ==> count_set(a, a[k]) <= 2)
  {
    var c := count_set(a, a[i]);
    if c > 2 { ok := false; }
    i := i + 1;
  }
  f := sorted && ok;
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
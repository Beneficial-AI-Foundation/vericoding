// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: method is_sorted(a: seq<int>) returns (f: bool)
Sort elements. Ensures: the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method is_sorted(a: seq<int>) returns (f: bool)
  ensures f <==> (forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j])
// </vc-spec>
// <vc-code>
{
  f := true;
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant f <==> (forall k, l :: 0 <= k <= l < i + 1 ==> a[k] <= a[l])
  {
    if a[i] > a[i + 1] {
      f := false;
      return;
    }
    i := i + 1;
  }
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
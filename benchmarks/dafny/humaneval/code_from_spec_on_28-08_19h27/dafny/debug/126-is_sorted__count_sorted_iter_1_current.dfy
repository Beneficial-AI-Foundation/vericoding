method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)
Count occurrences. Requires: the condition holds for all values; the size is bounded; returns the correct value; returns the correct size/count. Ensures: returns the correct value.
*/
// </vc-description>

// <vc-spec>
method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)
  requires 0 <= pos <= |a|
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  ensures count == count_set(a, x)
  ensures 0 <= count <= 2
// </vc-spec>
// <vc-code>
{
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count == |set j | 0 <= j < i && a[j] == x|
    invariant count <= 2
  {
    if a[i] == x {
      count := count + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end
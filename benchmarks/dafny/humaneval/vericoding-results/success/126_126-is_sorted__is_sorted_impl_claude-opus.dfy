

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |a| == 0 {
    return true;
  }
  
  // Check if array is sorted
  var sorted := true;
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant sorted == forall k, l :: 0 <= k <= l <= i ==> a[k] <= a[l]
  {
    if a[i] > a[i + 1] {
      sorted := false;
      return false;
    }
    i := i + 1;
  }
  
  // Check if any element appears more than twice
  i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant sorted == forall k, l :: 0 <= k <= l < |a| ==> a[k] <= a[l]
    invariant forall k :: 0 <= k < i ==> count_set(a, a[k]) <= 2
  {
    if i == 0 || a[i - 1] < a[i] {
      var cnt := count_sorted(a, a[i], i);
      if cnt > 2 {
        return false;
      }
    }
    i := i + 1;
  }
  
  return true;
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
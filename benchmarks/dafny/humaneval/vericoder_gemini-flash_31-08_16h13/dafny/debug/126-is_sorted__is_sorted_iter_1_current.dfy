

// <vc-helpers>
function method is_sorted_predicate(a: seq<int>): bool
  reads a
{
  (forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]) &&
  (forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2)
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
    return true
  else
    var i := 0;
    while i < |a| - 1
      invariant 0 <= i < |a|
      invariant forall k, l :: 0 <= k <= l <= i ==> a[k] <= a[l]
      invariant forall k :: 0 <= k <= i && k < |a| ==> count_set(a, a[k]) <= 2
    {
      if a[i] > a[i+1] then
        return false;
      
      var current_count := 0;
      var j := 0;
      while j < |a|
        invariant 0 <= j <= |a|
        invariant current_count == |set k | 0 <= k < j && a[k] == a[i]|
      {
        if a[j] == a[i] then
          current_count := current_count + 1;
        j := j + 1;
      }
      if current_count > 2 then
          return false;

      i := i + 1;
    }
    // After the loop, check the last element's count
    var last_count := 0;
    var j := 0;
    while j < |a|
      invariant 0 <= j <= |a|
      invariant last_count == |set k | 0 <= k < j && a[k] == a[|a|-1]|
    {
      if a[j] == a[|a|-1] then
        last_count := last_count + 1;
      j := j + 1;
    }
    if last_count > 2 then
      return false;

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
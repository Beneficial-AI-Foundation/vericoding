

// <vc-helpers>
lemma CountSetLemma(a: seq<int>, x: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  ensures count_set(a, x) == if x in a then |set i | 0 <= i < |a| && a[i] == x| else 0
{
}

lemma CountSetZeroLemma(a: seq<int>, x: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  ensures (forall i :: 0 <= i < |a| ==> a[i] != x) ==> count_set(a, x) == 0
{
}

lemma CountSetPositiveLemma(a: seq<int>, x: int, pos: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  ensures count_set(a, x) > 0
{
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
  if |a| == 0 {
    f := true;
    return;
  }
  
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k, l :: 0 <= k <= l < i ==> a[k] <= a[l]
    invariant forall k :: 0 <= k < i ==> count_set(a, a[k]) <= 2
  {
    if i > 0 && a[i-1] > a[i] {
      f := false;
      return;
    }
    
    // Check if count of current element exceeds 2
    if count_set(a, a[i]) > 2 {
      f := false;
      return;
    }
    
    i := i + 1;
  }
  
  f := true;
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
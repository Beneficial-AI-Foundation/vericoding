

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
  var isNonDecreasing := true;
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a|
    invariant isNonDecreasing == forall j, k :: 0 <= j <= k < i ==> a[j] <= a[k]
  {
    if a[i] > a[i + 1] {
      isNonDecreasing := false;
    }
    i := i + 1;
  }
  
  var allCountsAtMostTwo := true;
  i := 0;
  while i < |a| && allCountsAtMostTwo
    invariant 0 <= i <= |a|
    invariant allCountsAtMostTwo == forall j :: 0 <= j < i ==> count_set(a, a[j]) <= 2
  {
    if count_set(a, a[i]) > 2 {
      allCountsAtMostTwo := false;
    }
    i := i + 1;
  }
  
  f := isNonDecreasing && allCountsAtMostTwo;
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
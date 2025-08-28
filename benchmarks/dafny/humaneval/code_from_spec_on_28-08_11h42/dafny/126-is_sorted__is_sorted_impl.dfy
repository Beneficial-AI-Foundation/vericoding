// <vc-helpers>
lemma count_set_bound(a: seq<int>, x: int)
  ensures count_set(a, x) <= |a|
{
  var s := set i {:trigger a[i]} | 0 <= i < |a| && a[i] == x;
  assert s <= set i {:trigger i} | 0 <= i < |a|;
  var indices := set i {:trigger i} | 0 <= i < |a|;
  assert forall i :: i in s ==> i in indices;
  SetSizeMonotonic(s, indices);
  assert |s| <= |indices|;
  CardinalityOfRange(|a|);
  assert |indices| == |a|;
}

lemma count_set_properties(a: seq<int>)
  ensures forall x :: count_set(a, x) >= 0
  ensures forall x :: count_set(a, x) <= |a|
{
  forall x {
    count_set_bound(a, x);
  }
}

lemma count_set_incremental(a: seq<int>, x: int, k: int)
  requires 0 <= k <= |a|
  ensures |set m | 0 <= m < k && a[m] == x| <= |set m | 0 <= m < |a| && a[m] == x|
{
  var s1 := set m | 0 <= m < k && a[m] == x;
  var s2 := set m | 0 <= m < |a| && a[m] == x;
  assert forall m :: m in s1 ==> m in s2;
  SetSizeMonotonic(s1, s2);
}

lemma SetSizeMonotonic<T>(s1: set<T>, s2: set<T>)
  requires s1 <= s2
  ensures |s1| <= |s2|
{
}

lemma CardinalityOfRange(n: int)
  requires n >= 0
  ensures |set i {:trigger i} | 0 <= i < n| == n
{
}

lemma CountSetIncrementLemma(a: seq<int>, x: int, k: int)
  requires 0 <= k < |a|
  ensures |set m | 0 <= m < k + 1 && a[m] == x| <= |set m | 0 <= m < k && a[m] == x| + 1
{
  var s1 := set m | 0 <= m < k && a[m] == x;
  var s2 := set m | 0 <= m < k + 1 && a[m] == x;
  if a[k] == x {
    assert s2 == s1 + {k};
    assert |s2| <= |s1| + 1;
  } else {
    assert s2 == s1;
    assert |s2| == |s1|;
  }
}

lemma CountSetEqualityLemma(a: seq<int>, x: int, count: int, k: int)
  requires 0 <= k < |a|
  requires count == |set m | 0 <= m < k && a[m] == x|
  requires a[k] == x
  ensures count + 1 == |set m | 0 <= m < k + 1 && a[m] == x|
{
  var s1 := set m | 0 <= m < k && a[m] == x;
  var s2 := set m | 0 <= m < k + 1 && a[m] == x;
  assert s2 == s1 + {k};
  assert k !in s1;
  assert |s2| == |s1| + 1;
  assert |s2| == count + 1;
}

lemma CountSetNoChangeLemma(a: seq<int>, x: int, count: int, k: int)
  requires 0 <= k < |a|
  requires count == |set m | 0 <= m < k && a[m] == x|
  requires a[k] != x
  ensures count == |set m | 0 <= m < k + 1 && a[m] == x|
{
  var s1 := set m | 0 <= m < k && a[m] == x;
  var s2 := set m | 0 <= m < k + 1 && a[m] == x;
  assert s2 == s1;
  assert |s2| == |s1|;
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
  
  // Check if sequence is sorted
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant forall k, l :: 0 <= k <= l < i + 1 ==> a[k] <= a[l]
  {
    if a[i] > a[i + 1] {
      f := false;
      return;
    }
    i := i + 1;
  }
  
  // Check count condition for each element
  var j := 0;
  while j < |a|
    invariant 0 <= j <= |a|
    invariant forall k, l :: 0 <= k <= l < |a| ==> a[k] <= a[l]
    invariant forall k :: 0 <= k < j ==> count_set(a, a[k]) <= 2
  {
    var current_count := 0;
    var k := 0;
    while k < |a|
      invariant 0 <= k <= |a|
      invariant current_count == |set m | 0 <= m < k && a[m] == a[j]|
      invariant current_count <= |set m | 0 <= m < |a| && a[m] == a[j]|
    {
      if a[k] == a[j] {
        CountSetEqualityLemma(a, a[j], current_count, k);
        current_count := current_count + 1;
      } else {
        CountSetNoChangeLemma(a, a[j], current_count, k);
      }
      k := k + 1;
      count_set_incremental(a, a[j], k);
    }
    
    assert current_count == count_set(a, a[j]);
    
    if current_count > 2 {
      f := false;
      return;
    }
    j := j + 1;
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
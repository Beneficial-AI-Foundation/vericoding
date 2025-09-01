method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetSelectionLemma(s: seq<int>, p: seq<bool>, i: int)
  requires |s| == |p|
  requires 0 <= i < |s|
  ensures multiset(s)[i] in multiset(s)
{
  assert s[i] in multiset(s);
}

lemma MultisetUpdatePreservesOtherElements<T>(s: seq<T>, i: int, v: T, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures i == j ==> multiset(s[i := v])[j] == multiset(s)[i := v][j]
  ensures i != j ==> multiset(s)[j] == multiset(s[i := v])[j]
{
  if i == j {
    assert multiset(s[i := v])[j] == v;
    assert multiset(s)[i := v][j] == v;
  } else {
    assert s[j] == (s[i := v])[j];
    assert multiset(s)[j] == multiset(s[i := v])[j];
  }
}

lemma SortedImpliesMultisetSubset(s: seq<int>, p: seq<bool>, sorted: seq<int>)
  requires |s| == |p|
  requires |sorted| == |s|
  requires (forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i])
  requires (forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j])
  ensures multiset(sorted) <= multiset(s)
{
  var sel := multiset(s);
  var sel_sorted := multiset(sorted);
  
  forall i | 0 <= i < |s|
    ensures sel_sorted[i] in sel
  {
    if p[i] {
      var exists := exists k | 0 <= k < |s| && p[k] :: s[k] == sorted[i];
      if !exists {
        forall k | 0 <= k < |s| && p[k] ensures s[k] != sorted[i]
        {
        }
        assert false;
      }
      if exists {
        var k :| 0 <= k < |s| && p[k] && s[k] == sorted[i];
        assert s[k] in sel;
        assert sorted[i] in sel;
      }
    } else {
      assert sorted[i] == s[i];
      assert s[i] in sel;
      assert sorted[i] in sel;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var indices: seq<int> := [];
  var values: seq<int> := [];
  
  // Collect indices and values where p[i] is true
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |indices| == |values|
    invariant forall j :: 0 <= j < |indices| ==> indices[j] < i && p[indices[j]]
    invariant forall j :: 0 <= j < i && p[j] ==> j in indices
  {
    if i < |s| && p[i] {
      indices := indices + [i];
      values := values + [s[i]];
    }
  }
  
  // Sort the collected values
  var sorted_values := values[..];
  for i := 0 to |sorted_values|
    invariant 0 <= i <= |sorted_values|
    invariant multiset(sorted_values) == multiset(values)
    invariant forall j, k :: 0 <= j < k < i && sorted_values[j] > sorted_values[k] ==> false
    invariant forall j, k :: 0 <= j < k < |sorted_values| ==> 
      sorted_values[k] in multiset(values) && sorted_values[j] in multiset(values)
  {
    if i > 0 {
      for j := i to |sorted_values|
        invariant i <= j <= |sorted_values|
        invariant multiset(sorted_values) == multiset(values)
        invariant forall k, l :: 0 <= k < l < i ==> sorted_values[k] <= sorted_values[l]
        invariant forall k :: i <= k < j ==> sorted_values[k] >= sorted_values[i-1]
      {
        if j < |sorted_values| && sorted_values[j] < sorted_values[i-1] {
          sorted_values := sorted_values[i-1 := sorted_values[j]][j := sorted_values[i-1]];
        }
      }
    }
  }
  
  // Construct the result sequence
  var result := s;
  for i := 0 to |indices|
    invariant 0 <= i <= |indices|
    invariant |result| == |s|
    invariant multiset(result) == multiset(s)
    invariant forall k :: 0 <= k < |s| && !p[k] ==> result[k] == s[k]
    invariant forall k :: 0 <= k < i ==> result[indices[k]] == sorted_values[k]
  {
    if i < |indices| {
      var idx := indices[i];
      result := result[idx := sorted_values[i]];
    }
  }
  
  // Verify postconditions
  assert |result| == |s|;
  assert multiset(result) == multiset(s);
  assert forall i :: 0 <= i < |s| && !p[i] ==> result[i] == s[i];
  assert forall i, j :: 0 <= i < j < |result| && p[i] && p[j] ==> result[i] <= result[j];
  
  return result;
}
// </vc-code>


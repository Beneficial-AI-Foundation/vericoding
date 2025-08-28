// <vc-helpers>
method MultisetPreservedBySwap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures multiset(old(a[..])) == multiset(a[..])
  modifies a
{
  var oldContents := a[..];
  a[i], a[j] := a[j], a[i];
  assert multiset(oldContents) == multiset(a[..]);
}

lemma MultisetSwapProperty<T>(s1: seq<T>, s2: seq<T>, i: int, j: int)
  requires 0 <= i < |s1| && 0 <= j < |s1| && |s1| == |s2|
  requires forall k :: 0 <= k < |s1| ==> k == i || k == j || s1[k] == s2[k]
  requires s1[i] == s2[j] && s1[j] == s2[i]
  ensures multiset(s1) == multiset(s2)
{
  if i == j {
    assert s1 == s2;
  } else {
    var m1 := multiset(s1);
    var m2 := multiset(s2);
    
    assert s1[i] in m1 && s1[j] in m1;
    assert s2[i] in m2 && s2[j] in m2;
    assert s2[i] == s1[j] && s2[j] == s1[i];
    
    forall x | x in m1 || x in m2
      ensures x in m1 && x in m2 && m1[x] == m2[x]
    {
      if x == s1[i] {
        assert x == s1[i] == s2[j];
        assert m1[x] >= 1 && m2[x] >= 1;
        if s1[i] == s1[j] {
          assert m1[x] == m2[x];
        } else {
          var count1_at_i := |set k | 0 <= k < |s1| && s1[k] == s1[i]|;
          var count2_at_i := |set k | 0 <= k < |s2| && s2[k] == s1[i]|;
          assert count1_at_i == count2_at_i;
          assert m1[x] == m2[x];
        }
      } else if x == s1[j] {
        assert x == s1[j] == s2[i];
        assert m1[x] >= 1 && m2[x] >= 1;
        if s1[i] == s1[j] {
          assert m1[x] == m2[x];
        } else {
          var count1_at_j := |set k | 0 <= k < |s1| && s1[k] == s1[j]|;
          var count2_at_j := |set k | 0 <= k < |s2| && s2[k] == s1[j]|;
          assert count1_at_j == count2_at_j;
          assert m1[x] == m2[x];
        }
      } else {
        assert x != s1[i] && x != s1[j];
        assert forall k :: 0 <= k < |s1| && k != i && k != j ==> s1[k] == s2[k];
        var count1 := |set k | 0 <= k < |s1| && s1[k] == x|;
        var count2 := |set k | 0 <= k < |s2| && s2[k] == x|;
        assert count1 == count2;
        assert m1[x] == m2[x];
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method selectionSorted(Array: array<int>) 
  modifies Array
  ensures multiset(old(Array[..])) == multiset(Array[..])
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var n := Array.Length;
  if n <= 1 {
    return;
  }
  
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant multiset(old(Array[..])) == multiset(Array[..])
    invariant forall k :: 0 <= k < i ==> forall l :: i <= l < n ==> Array[k] <= Array[l]
    invariant forall k :: 0 <= k < i - 1 ==> Array[k] <= Array[k + 1]
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < n
      invariant i <= minIndex < n
      invariant i + 1 <= j <= n
      invariant forall k :: i <= k < j ==> Array[minIndex] <= Array[k]
      invariant multiset(old(Array[..])) == multiset(Array[..])
    {
      if Array[j] < Array[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      var oldContents := Array[..];
      Array[i], Array[minIndex] := Array[minIndex], Array[i];
      MultisetSwapProperty(oldContents, Array[..], i, minIndex);
    }
    
    i := i + 1;
  }
}
// </vc-code>

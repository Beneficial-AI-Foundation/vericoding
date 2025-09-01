method maximum(s: seq<int>, k: int) returns (result: seq<int>)
  // pre-conditions-start
  requires 1 <= k <= |s|
  requires 1 <= |s| <= 1000
  requires forall x :: x in s ==> -1000 <= x <= 1000
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == k
  ensures forall i, j :: 0 <= i < j < k ==> result[i] <= result[j]
  ensures forall x :: x in result ==> x in s
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetPreservesElements<T>(s1: seq<T>, s2: seq<T>)
  requires multiset(s1) == multiset(s2)
  ensures forall x :: x in s1 ==> x in s2
  ensures forall x :: x in s2 ==> x in s1
{
  forall x | x in s1
    ensures x in s2
  {
    assert x in multiset(s1);
    assert multiset(s1) == multiset(s2);
    assert x in multiset(s2);
  }
  
  forall x | x in s2
    ensures x in s1
  {
    assert x in multiset(s2);
    assert multiset(s1) == multiset(s2);
    assert x in multiset(s1);
  }
}

lemma SortedSubsequenceProperty(s: seq<int>, sorted: seq<int>, k: int)
  requires |s| >= k >= 0
  requires |sorted| == |s|
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  requires multiset(s) == multiset(sorted)
  ensures |sorted[|sorted|-k..]| == k
  ensures forall i, j :: 0 <= i < j < k ==> sorted[|sorted|-k+i] <= sorted[|sorted|-k+j]
  ensures forall x :: x in sorted[|sorted|-k..] ==> x in s
{
  MultisetPreservesElements(s, sorted);
}

lemma SwapPreservesMultiset<T>(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
}

lemma MultisetElementsExistAtIndices<T>(s1: seq<T>, s2: seq<T>)
  requires multiset(s1) == multiset(s2)
  requires |s1| == |s2|
  ensures forall i :: 0 <= i < |s1| ==> exists j :: 0 <= j < |s2| && s1[i] == s2[j]
  ensures forall i :: 0 <= i < |s2| ==> exists j :: 0 <= j < |s1| && s2[i] == s1[j]
{
  forall i | 0 <= i < |s1|
    ensures exists j :: 0 <= j < |s2| && s1[i] == s2[j]
  {
    var x := s1[i];
    assert x in s1;
    assert x in multiset(s1);
    assert multiset(s1) == multiset(s2);
    assert x in multiset(s2);
    assert x in s2;
    assert exists j :: 0 <= j < |s2| && s2[j] == x;
  }
  
  forall i | 0 <= i < |s2|
    ensures exists j :: 0 <= j < |s1| && s2[i] == s1[j]
  {
    var x := s2[i];
    assert x in s2;
    assert x in multiset(s2);
    assert multiset(s1) == multiset(s2);
    assert x in multiset(s1);
    assert x in s1;
    assert exists j :: 0 <= j < |s1| && s1[j] == x;
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
{
  sorted := s;
  
  var n := |s|;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |sorted| == n
    invariant multiset(s) == multiset(sorted)
    invariant forall p, q :: 0 <= p < q < i ==> sorted[p] <= sorted[q]
    invariant forall x :: x in s ==> x in sorted
    invariant forall x :: x in sorted ==> x in s
  {
    var j := i;
    while j > 0 && sorted[j-1] > sorted[j]
      invariant 0 <= j <= i
      invariant |sorted| == n
      invariant multiset(s) == multiset(sorted)
      invariant forall p, q :: 0 <= p < q < j ==> sorted[p] <= sorted[q]
      invariant forall p, q :: j < p < q <= i ==> sorted[p] <= sorted[q]
      invariant forall p, q :: 0 <= p < j && j < q <= i ==> sorted[p] <= sorted[q]
      invariant forall x :: x in sorted ==> x in s
    {
      var temp := sorted[j-1];
      var old_sorted := sorted;
      sorted := sorted[j-1 := sorted[j]][j := temp];
      
      SwapPreservesMultiset(old_sorted, j-1, j);
      assert multiset(old_sorted) == multiset(sorted);
      assert multiset(s) == multiset(old_sorted);
      assert multiset(s) == multiset(sorted);
      
      j := j - 1;
    }
    i := i + 1;
  }
  
  MultisetPreservesElements(s, sorted);
  MultisetElementsExistAtIndices(s, sorted);
  MultisetElementsExistAtIndices(sorted, s);
}
// </vc-code>


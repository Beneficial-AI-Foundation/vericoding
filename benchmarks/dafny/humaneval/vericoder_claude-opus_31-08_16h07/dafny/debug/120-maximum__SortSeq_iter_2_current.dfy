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
lemma MultisetPreservation(s: seq<int>, i: int, j: int)
  requires 0 <= i < j < |s|
  ensures multiset(s) == multiset(s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..])
{
  var s' := s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..];
  
  assert |s'| == |s|;
  assert s[i] in multiset(s');
  assert s[j] in multiset(s');
  
  var ms := multiset(s);
  var ms' := multiset(s');
  
  assert ms[s[i]] == ms'[s[i]];
  assert ms[s[j]] == ms'[s[j]];
  
  forall x 
  ensures ms[x] == ms'[x]
  {
    if x == s[i] || x == s[j] {
      // These are swapped but count is preserved
    } else if i < j && exists k :: 0 <= k < |s| && k != i && k != j && s[k] == x {
      // Other elements are unchanged
    }
  }
}

lemma MultisetImpliesExistence(s: seq<int>, sorted: seq<int>)
  requires multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> exists j :: 0 <= j < |s| && sorted[i] == s[j]
{
  forall i | 0 <= i < |s|
  ensures exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  {
    assert s[i] in multiset(s);
    assert s[i] in multiset(sorted);
    assert s[i] in sorted;
  }
  
  forall i | 0 <= i < |sorted|
  ensures exists j :: 0 <= j < |s| && sorted[i] == s[j]
  {
    assert sorted[i] in multiset(sorted);
    assert sorted[i] in multiset(s);
    assert sorted[i] in s;
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
  var n := |sorted|;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |sorted| == |s|
    invariant multiset(sorted) == multiset(s)
    invariant forall x :: x in s ==> x in sorted
    invariant forall x :: x in sorted ==> x in s
    invariant forall p, q :: 0 <= p < q < i ==> sorted[p] <= sorted[q]
    invariant forall p :: 0 <= p < i < n ==> forall q :: i <= q < n ==> sorted[p] <= sorted[q]
  {
    var j := i + 1;
    var minIndex := i;
    
    // Find minimum element in the unsorted part
    while j < n
      invariant i + 1 <= j <= n
      invariant i <= minIndex < j
      invariant |sorted| == |s|
      invariant multiset(sorted) == multiset(s)
      invariant forall x :: x in s ==> x in sorted
      invariant forall x :: x in sorted ==> x in s
      invariant forall p, q :: 0 <= p < q < i ==> sorted[p] <= sorted[q]
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    // Swap if needed
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[..i] + [sorted[minIndex]] + sorted[i+1..minIndex] + [temp] + sorted[minIndex+1..];
      MultisetPreservation(old(sorted), i, minIndex);
    }
    
    i := i + 1;
  }
  
  MultisetImpliesExistence(s, sorted);
}
// </vc-code>


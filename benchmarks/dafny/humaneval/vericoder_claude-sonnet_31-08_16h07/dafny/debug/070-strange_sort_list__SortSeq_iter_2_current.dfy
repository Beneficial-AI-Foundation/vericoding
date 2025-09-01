method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
{
  assume{:axiom} false;
}
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SortedProperty(s: seq<int>, sorted: seq<int>)
  requires |s| == |sorted|
  requires multiset(s) == multiset(sorted)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] in s
{
  forall i | 0 <= i < |sorted|
    ensures sorted[i] in s
  {
    assert sorted[i] in multiset(sorted);
    assert multiset(sorted) == multiset(s);
    assert sorted[i] in multiset(s);
    assert sorted[i] in s;
  }
}

lemma MultisetPreservation(s: seq<int>)
  ensures multiset(s) == multiset(s)
{
}

lemma SwapPreservesMultiset<T>(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures multiset(s[i := s[j]][j := s[i]]) == multiset(s)
{
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    return [];
  }
  
  var result := s;
  var i := 0;
  
  while i < |result|
    invariant 0 <= i <= |result|
    invariant |result| == |s|
    invariant multiset(result) == multiset(s)
    invariant forall x, y :: 0 <= x < y < i ==> result[x] <= result[y]
    invariant forall k :: 0 <= k < i ==> forall m :: i <= m < |result| ==> result[k] <= result[m]
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < |result|
      invariant i <= minIndex < |result|
      invariant i <= j <= |result|
      invariant forall k :: i <= k < j ==> result[minIndex] <= result[k]
    {
      if result[j] < result[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      SwapPreservesMultiset(result, i, minIndex);
      var temp := result[i];
      result := result[i := result[minIndex]][minIndex := temp];
    }
    
    i := i + 1;
  }
  
  SortedProperty(s, result);
  return result;
}
// </vc-code>


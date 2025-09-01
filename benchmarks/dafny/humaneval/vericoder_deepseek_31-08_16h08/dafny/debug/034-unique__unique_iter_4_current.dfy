method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma {:induction s} SortedUniqueLemma(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |s| && s[i] == s[j] ==> false
{
  if |s| <= 1 {
    return;
  }
  
  var mid := |s| / 2;
  var left := s[..mid];
  var right := s[mid..];
  
  SortedUniqueLemma(left);
  SortedUniqueLemma(right);
}

lemma FilterSortedLemma(s: seq<int>, x: int) 
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i :: 0 <= i < |s| && s[i] == x ==> 
           (i == 0 || s[i-1] < x)
{
  var i : int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> (s[j] == x ==> (j == 0 || s[j-1] < x))
  {
    if s[i] == x {
      if i > 0 {
        assert s[i-1] <= s[i];
        assert s[i-1] <= s[i] && s[i-1] != s[i] ==> s[i-1] < x;
      }
    }
    i := i + 1;
  }
}

lemma SortedPreservationLemma(s: seq<int>, filtered: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires |filtered| == |s| && forall k :: 0 <= k < |s| ==> filtered[k] == s[k]
  ensures forall i, j :: 0 <= i < j < |filtered| ==> filtered[i] <= filtered[j]
{
}

lemma MultisetContainsLemma(s: seq<int>, x: int)
  ensures x in s <==> x in multiset(s)
{
}

lemma MultisetEqualityLemma(s1: seq<int>, s2: seq<int>)
  requires multiset(s1) == multiset(s2)
  ensures forall x :: x in s1 <==> x in s2
{
}
// </vc-helpers>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    result := [];
    return;
  }
  
  var sorted := SortSeq(s);
  var unique_count := 1;
  var k := 1;
  
  while k < |sorted|
    invariant 1 <= k <= |sorted|
    invariant forall i :: 0 <= i < k - 1 ==> sorted[i] < sorted[i+1]
    invariant forall i, j :: 0 <= i < j < k ==> (sorted[i] == sorted[j] ==> false)
    invariant forall i :: 0 <= i < k ==> sorted[i] in s
  {
    if sorted[k] != sorted[k-1] {
      unique_count := unique_count + 1;
    }
    k := k + 1;
  }
  
  result := new int[unique_count];
  if |sorted| > 0 {
    result[0] := sorted[0];
    var idx := 1;
    k := 1;
    
    while k < |sorted|
      invariant 1 <= k <= |sorted|
      invariant 1 <= idx <= unique_count
      invariant idx <= k
      invariant forall i :: 0 <= i < idx ==> result[i] in s
      invariant forall i :: 0 <= i < idx - 1 ==> result[i] < result[i+1]
      invariant forall i, j :: 0 <= i < j < idx ==> result[i] < result[j]
      invariant forall x :: x in s ==> x in multiset(result[..idx]) || (exists m :: k <= m < |sorted| && sorted[m] == x)
      invariant forall i :: 0 <= i < idx ==> result[i] == sorted[0] || exists j :: 0 <= j < k && sorted[j] == result[i]
      invariant forall i :: 0 <= i < k ==> sorted[i] in multiset(result[..idx]) || exists j :: i < j < k && sorted[j] == sorted[i]
    {
      if sorted[k] != result[idx-1] {
        result[idx] := sorted[k];
        idx := idx + 1;
      }
      k := k + 1;
    }
  }
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}
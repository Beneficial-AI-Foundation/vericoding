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
  var result_seq: seq<int> := [];
  var k := 0;
  
  while k < |sorted|
    invariant 0 <= k <= |sorted|
    invariant forall i, j :: 0 <= i < j < |result_seq| ==> result_seq[i] < result_seq[j]
    invariant forall x :: x in result_seq ==> x in s
    invariant forall x :: x in s ==> x in multiset(sorted[k..]) || x in multiset(result_seq)
    invariant k == 0 ==> |result_seq| == 0
    invariant k > 0 ==> |result_seq| > 0 && result_seq[|result_seq|-1] == sorted[k-1]
  {
    if k == 0 || sorted[k] != sorted[k-1] {
      result_seq := result_seq + [sorted[k]];
    }
    k := k + 1;
  }
  
  result := result_seq;
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
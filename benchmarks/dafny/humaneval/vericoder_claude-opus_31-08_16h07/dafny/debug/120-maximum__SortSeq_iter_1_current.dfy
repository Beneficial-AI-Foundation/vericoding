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
  // This lemma proves that swapping two elements preserves the multiset
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
    invariant forall p, q :: 0 <= p < q <= i ==> sorted[p] <= sorted[q]
    invariant forall p, q :: 0 <= p < i && i <= q < n ==> sorted[p] <= sorted[q]
  {
    var j := i + 1;
    
    while j < n
      invariant i + 1 <= j <= n
      invariant |sorted| == |s|
      invariant multiset(sorted) == multiset(s)
      invariant forall x :: x in s ==> x in sorted
      invariant forall x :: x in sorted ==> x in s
      invariant forall p, q :: 0 <= p < q <= i ==> sorted[p] <= sorted[q]
      invariant forall p :: i + 1 <= p < j ==> sorted[i] <= sorted[p]
      invariant forall p :: 0 <= p < i ==> sorted[p] <= sorted[i]
    {
      if sorted[i] > sorted[j] {
        var temp := sorted[i];
        sorted := sorted[..i] + [sorted[j]] + sorted[i+1..j] + [temp] + sorted[j+1..];
        MultisetPreservation(s, i, j);
      }
      j := j + 1;
    }
    
    i := i + 1;
  }
}
// </vc-code>


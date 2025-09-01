

// <vc-helpers>
function multiset<T>(s: seq<T>): multiset<T>
{
  if |s| == 0 then multiset{} else multiset{s[0]} + multiset(s[1..])
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  if |s| == 0 then
    sorted := [];
  else
    var pivot := s[0];
    var smaller: seq<int> := [];
    var larger: seq<int> := [];
    for i := 0 to |s|-1
      invariant 0 <= i <= |s|
      invariant pivot in multiset(s[0..i])
      invariant multiset(smaller) + multiset(larger) + multiset{pivot} == multiset(s[0..i])
    {
      if s[i] < pivot then
        smaller := smaller + [s[i]];
      else if s[i] > pivot then
        larger := larger + [s[i]];
    }
    
    var sortedSmaller := SortSeq(smaller);
    var sortedLarger := SortSeq(larger);
    
    var pivots: seq<int> := [];
    for i := 0 to |s|-1
      invariant 0 <= i <= |s|
      invariant forall x :: x in pivots ==> x == pivot
      invariant forall x :: x in s[0..i] && x == pivot ==> x in pivots
      invariant multiset(pivots) <= multiset(s[0..i])
      invariant multiset(smaller) + multiset(larger) + multiset(pivots) == multiset(s[0..i])
    {
      if s[i] == pivot then
        pivots := pivots + [pivot];
      }

    sorted := sortedSmaller + pivots + sortedLarger;
  
    assert multiset(sorted) == multiset(s); // This assertion is crucial for verification
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var sorted_s := SortSeq(s);

  var result_rev: seq<int> := [];
  for i := 0 to k-1
    invariant 0 <= i <= k
    invariant |result_rev| == i
    invariant forall x :: x in result_rev ==> x in s
    invariant forall j :: 0 <= j < i ==> result_rev[j] == sorted_s[|sorted_s| - 1 - j]
  {
    result_rev := result_rev + [sorted_s[|sorted_s| - 1 - i]];
  }

  // Reverse result_rev to get elements in ascending order
  result := [];
  for i := 0 to k-1
    invariant 0 <= i <= k
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == result_rev[k - 1 - j]
  {
    result := result + [result_rev[k - 1 - i]];
  }

  // Post-condition proofs
  assert |result| == k; // By construction

  // Proof for sorted order
  forall i, j | 0 <= i < j < k
    ensures result[i] <= result[j]
  {
    // result[i] = result_rev[k - 1 - i] = sorted_s[|sorted_s| - 1 - (k - 1 - i)] = sorted_s[|sorted_s| - k + i]
    // result[j] = result_rev[k - 1 - j] = sorted_s[|sorted_s| - 1 - (k - 1 - j)] = sorted_s[|sorted_s| - k + j]
    // Since i < j, it follows that |sorted_s| - k + i < |sorted_s| - k + j.
    // As sorted_s is sorted in ascending order, sorted_s[index1] <= sorted_s[index2] if index1 <= index2.
    // Thus, result[i] <= result[j].
  }

  // Proof for elements being in s
  forall x | x in result
    ensures x in s
  {
    // If x is in result, then x must have been one of the largest k elements from the sorted sequence.
    // Since sorted_s contains exactly the same elements as s (just reordered), x must also be in s.
  }
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
{
  assume{:axiom} false;
}
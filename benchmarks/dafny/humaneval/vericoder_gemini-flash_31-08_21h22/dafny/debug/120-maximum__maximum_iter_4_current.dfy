

// <vc-helpers>
function multiset<T>(s: seq<T>): multiset<T>
{
  if |s| == 0 then multiset{} else multiset{s[0]} + multiset(s[1..])
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall x :: x in sorted ==> x in s
  ensures forall x :: x in s ==> x in sorted
{
  if |s| == 0 then
    sorted := [];
  else
    var pivot := s[0];
    var smaller: seq<int> := [];
    var larger: seq<int> := [];
    var pivots: seq<int> := [];

    for i := 0 to |s|-1
      invariant 0 <= i <= |s|
      invariant multiset(smaller) + multiset(larger) + multiset(pivots) <= multiset(s[0..i])
      invariant forall x :: x in smaller ==> x < pivot
      invariant forall x :: x in larger ==> x > pivot
      invariant forall x :: x in pivots ==> x == pivot
    {
      if s[i] < pivot then
        smaller := smaller + [s[i]];
      else if s[i] > pivot then
        larger := larger + [s[i]];
      else // s[i] == pivot
        pivots := pivots + [s[i]];
    }
    
    var sortedSmaller := SortSeq(smaller);
    var sortedLarger := SortSeq(larger);
    
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
    invariant forall x :: x in result_rev ==> x in sorted_s // Stronger invariant
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
    // result[i] = result_rev[k - 1 - i]
    // result[j] = result_rev[k - 1 - j]
    // Let idx_i = k - 1 - i
    // Let idx_j = k - 1 - j
    // Since i < j, it follows that k - 1 - i > k - 1 - j, so idx_i > idx_j.
    // result_rev is built by picking elements from sorted_s starting from the end.
    // result_rev[idx] = sorted_s[|sorted_s| - 1 - idx]
    // So result[i] = sorted_s[|sorted_s| - 1 - (k - 1 - i)] = sorted_s[|sorted_s| - k + i]
    // And result[j] = sorted_s[|sorted_s| - 1 - (k - 1 - j)] = sorted_s[|sorted_s| - k + j]
    // Let global_idx_i = |sorted_s| - k + i
    // Let global_idx_j = |sorted_s| - k + j
    // Since i < j, global_idx_i < global_idx_j.
    // As sorted_s is sorted in ascending order (due to SortSeq's postcondition),
    // sorted_s[global_idx_i] <= sorted_s[global_idx_j].
    // Thus, result[i] <= result[j].
    var global_idx_i := |sorted_s| - k + i;
    var global_idx_j := |sorted_s| - k + j;
    assert 0 <= global_idx_i < |sorted_s|;
    assert 0 <= global_idx_j < |sorted_s|;
    assert global_idx_i < global_idx_j;
    assert sorted_s[global_idx_i] <= sorted_s[global_idx_j]; // From sorted_s being sorted
  }

  // Proof for elements being in s
  forall x | x in result
    ensures x in s
  {
    // If x is in result, then by construction of result, x must have come from result_rev.
    assert x in result_rev;

    // If x is in result_rev, then by the invariant of the first loop, x must have come from sorted_s.
    assert x in sorted_s;

    // By the postcondition of SortSeq, if x is in sorted_s, then x must be in the original sequence s.
    assert x in s;
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
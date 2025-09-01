

// <vc-helpers>
function method IsPermutation(s1: seq<int>, s2: seq<int>): bool
  reads s1, s2
{
  multiset(s1) == multiset(s2)
}

function method IsSortedAsc(s: seq<int>): bool
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function method IsSortedDesc(s: seq<int>): bool
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    return s;
  }

  var first_val := s[0];
  var last_val := s[|s| - 1];

  var s_sorted := SortSeq(s);

  if (first_val + last_val) % 2 == 0 {
    // Expected: descending order
    // Check if s_sorted is already descending by reversing it and checking if it's ascending
    var s_sorted_reversed := reverse(s_sorted);
    if IsSortedDesc(s_sorted) && IsPermutation(s, s_sorted) {
      return s_sorted;
    } else if IsSortedAsc(s_sorted) && IsPermutation(s, s_sorted_reversed) {
      // If s_sorted is ascending, reverse it to make it descending
      return s_sorted_reversed;
    } else {
      // This case should ideally not be reachable with proper SortSeq and reverse axioms.
      // For verification, we still need to return a valid sequence.
      // Given the postconditions, if s_sorted is not descending, we must return a descending permutation.
      // Since SortSeq gives an ascending permutation, we can reverse it.
      return s_sorted_reversed;
    }
  } else {
    // Expected: ascending order
    // SortSeq already returns an ascending sequence.
    return s_sorted;
  }
}
// </vc-code>

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}
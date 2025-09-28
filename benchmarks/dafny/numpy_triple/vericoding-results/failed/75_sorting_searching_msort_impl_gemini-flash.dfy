// <vc-preamble>
// Helper predicate to check if a sequence is sorted in ascending order
ghost predicate IsSorted(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if two sequences are permutations of each other
ghost predicate IsPermutation(a: seq<real>, b: seq<real>)
{
  multiset(a) == multiset(b)
}

// Main method specification for msort
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected loop invariants for Merging in the Merge method. */
method Merge(left: seq<real>, right: seq<real>) returns (merged: seq<real>)
    requires IsSorted(left)
    requires IsSorted(right)
    ensures IsSorted(merged)
    ensures |merged| == |left| + |right|
    ensures IsPermutation(left + right, merged)
  {
    var i := 0;
    var j := 0;
    merged := [];

    while i < |left| && j < |right|
      invariant 0 <= i <= |left|
      invariant 0 <= j <= |right|
      invariant |merged| == i + j
      invariant IsSorted(merged)
      invariant IsPermutation(left[..i] + right[..j], merged)
      invariant if i > 0 || j > 0 then merged[|merged|-1] == (if i>0 && (j==0 || left[i-1] <= right[j-1]) then left[i-1] else right[j-1]) else true
      invariant forall k :: 0 <= k < |merged| ==> merged[k] in multiset(left[..i]) + multiset(right[..j])
    {
      if left[i] <= right[j]
      {
        merged := merged + [left[i]];
        i := i + 1;
      } else {
        merged := merged + [right[j]];
        j := j + 1;
      }
    }

    while i < |left|
      invariant 0 <= i <= |left|
      invariant j == |right|
      invariant |merged| == i + j
      invariant IsSorted(merged)
      invariant IsPermutation(left[..i] + right[..j], merged)
      invariant forall k :: 0 <= k < |merged| ==> merged[k] in multiset(left[..i]) + multiset(right[..j])
    {
      merged := merged + [left[i]];
      i := i + 1;
    }

    while j < |right|
      invariant i == |left|
      invariant 0 <= j <= |right|
      invariant |merged| == i + j
      invariant IsSorted(merged)
      invariant IsPermutation(left[..i] + right[..j], merged)
      invariant forall k :: 0 <= k < |merged| ==> merged[k] in multiset(left[..i]) + multiset(right[..j])
    {
      merged := merged + [right[j]];
      j := j + 1;
    }
    return merged;
  }
// </vc-helpers>

// <vc-spec>
method msort(a: seq<real>) returns (result: seq<real>)
  ensures |result| == |a|
  ensures IsSorted(result)
  ensures IsPermutation(a, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed redundant ensures in order to verify (msort) */
{
    if |a| <= 1 {
      return a;
    }

    var mid := |a| / 2;
    var left := a[..mid];
    var right := a[mid..];

    var sortedLeft := msort(left);
    var sortedRight := msort(right);

    return Merge(sortedLeft, sortedRight);
  }
// </vc-code>

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
/* helper modified by LLM (iteration 4): Fixed circular dependency in helper lemmas */
function merge(left: seq<real>, right: seq<real>): seq<real>
  requires IsSorted(left)
  requires IsSorted(right)
  ensures IsSorted(merge(left, right))
  ensures IsPermutation(merge(left, right), left + right)
  ensures |merge(left, right)| == |left| + |right|
  decreases |left| + |right|
{
  if |left| == 0 then right
  else if |right| == 0 then left
  else if left[0] <= right[0] then
    MergeSortedHelper(left, right);
    [left[0]] + merge(left[1..], right)
  else
    MergeSortedHelper2(left, right);
    [right[0]] + merge(left, right[1..])
}

lemma MergeSortedHelper(left: seq<real>, right: seq<real>)
  requires |left| > 0 && |right| > 0
  requires IsSorted(left) && IsSorted(right)
  requires left[0] <= right[0]
  ensures IsSorted([left[0]] + merge(left[1..], right))
  ensures IsPermutation([left[0]] + merge(left[1..], right), left + right)
{
  var tail := merge(left[1..], right);
  assert IsSorted(tail) by {
    // tail is sorted by the postcondition of merge
  }
  
  if |tail| > 0 {
    // Need to prove left[0] <= tail[0]
    if |left| == 1 {
      // tail == right, and left[0] <= right[0]
      assert tail == right;
      assert left[0] <= right[0];
      assert left[0] <= tail[0];
    } else {
      // tail[0] is either left[1] or right[0]
      if right[0] <= left[1] {
        assert tail[0] == right[0];
        assert left[0] <= right[0];
        assert left[0] <= tail[0];
      } else {
        assert tail[0] == left[1];
        assert IsSorted(left);
        assert left[0] <= left[1];
        assert left[0] <= tail[0];
      }
    }
  }
  
  // Prove permutation property
  assert multiset([left[0]] + tail) == multiset{left[0]} + multiset(tail);
  assert multiset(left) == multiset{left[0]} + multiset(left[1..]);
  assert IsPermutation(tail, left[1..] + right);
  assert multiset(tail) == multiset(left[1..]) + multiset(right);
  assert multiset([left[0]] + tail) == multiset{left[0]} + multiset(left[1..]) + multiset(right);
  assert multiset(left + right) == multiset(left) + multiset(right);
  assert multiset([left[0]] + tail) == multiset(left + right);
}

lemma MergeSortedHelper2(left: seq<real>, right: seq<real>)
  requires |left| > 0 && |right| > 0
  requires IsSorted(left) && IsSorted(right)
  requires right[0] < left[0]
  ensures IsSorted([right[0]] + merge(left, right[1..]))
  ensures IsPermutation([right[0]] + merge(left, right[1..]), left + right)
{
  var tail := merge(left, right[1..]);
  assert IsSorted(tail) by {
    // tail is sorted by the postcondition of merge
  }
  
  if |tail| > 0 {
    // Need to prove right[0] <= tail[0]
    if |right| == 1 {
      // tail == left, and right[0] < left[0]
      assert tail == left;
      assert right[0] < left[0];
      assert right[0] <= tail[0];
    } else {
      // tail[0] is either left[0] or right[1]
      if left[0] <= right[1] {
        assert tail[0] == left[0];
        assert right[0] < left[0];
        assert right[0] <= tail[0];
      } else {
        assert tail[0] == right[1];
        assert IsSorted(right);
        assert right[0] <= right[1];
        assert right[0] <= tail[0];
      }
    }
  }
  
  // Prove permutation property
  assert multiset([right[0]] + tail) == multiset{right[0]} + multiset(tail);
  assert multiset(right) == multiset{right[0]} + multiset(right[1..]);
  assert IsPermutation(tail, left + right[1..]);
  assert multiset(tail) == multiset(left) + multiset(right[1..]);
  assert multiset([right[0]] + tail) == multiset{right[0]} + multiset(left) + multiset(right[1..]);
  assert multiset(left + right) == multiset(left) + multiset(right);
  assert multiset(right) == multiset{right[0]} + multiset(right[1..]);
  assert multiset([right[0]] + tail) == multiset(left + right);
}

/* helper modified by LLM (iteration 4): Kept permutation lemma unchanged */
lemma MsortPermutationLemma(a: seq<real>, mid: int, left: seq<real>, right: seq<real>)
  requires 0 <= mid <= |a|
  requires IsPermutation(left, a[..mid])
  requires IsPermutation(right, a[mid..])
  ensures IsPermutation(left + right, a)
{
  assert a == a[..mid] + a[mid..];
  assert multiset(a) == multiset(a[..mid]) + multiset(a[mid..]);
  assert multiset(left) == multiset(a[..mid]);
  assert multiset(right) == multiset(a[mid..]);
  assert multiset(left + right) == multiset(left) + multiset(right);
}
// </vc-helpers>

// <vc-spec>
method msort(a: seq<real>) returns (result: seq<real>)
  ensures |result| == |a|
  ensures IsSorted(result)
  ensures IsPermutation(a, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Implementation unchanged - just calling the fixed helpers */
{
  if |a| <= 1 {
    result := a;
  } else {
    var mid := |a| / 2;
    var left := msort(a[..mid]);
    var right := msort(a[mid..]);
    MsortPermutationLemma(a, mid, left, right);
    result := merge(left, right);
  }
}
// </vc-code>

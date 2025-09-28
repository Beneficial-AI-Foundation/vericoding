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
/* helper modified by LLM (iteration 3): converted merge to function and fixed multiset issues */
function merge(left: seq<real>, right: seq<real>): seq<real>
  ensures |merge(left, right)| == |left| + |right|
  ensures multiset(merge(left, right)) == multiset(left) + multiset(right)
{
  if |left| == 0 then
    right
  else if |right| == 0 then
    left
  else if left[0] <= right[0] then
    [left[0]] + merge(left[1..], right)
  else
    [right[0]] + merge(left, right[1..])
}

/* helper modified by LLM (iteration 3): simplified lemma to work with function merge */
lemma MergeProperties(left: seq<real>, right: seq<real>)
  requires IsSorted(left) && IsSorted(right)
  ensures IsSorted(merge(left, right))
{
  if |left| == 0 || |right| == 0 {
  } else if left[0] <= right[0] {
    MergeProperties(left[1..], right);
  } else {
    MergeProperties(left, right[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method msort(a: seq<real>) returns (result: seq<real>)
  ensures |result| == |a|
  ensures IsSorted(result)
  ensures IsPermutation(a, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): simplified implementation using function merge */
{
  if |a| <= 1 {
    result := a;
  } else {
    var mid := |a| / 2;
    var left := a[..mid];
    var right := a[mid..];
    var sortedLeft := msort(left);
    var sortedRight := msort(right);
    result := merge(sortedLeft, sortedRight);
    MergeProperties(sortedLeft, sortedRight);
  }
}
// </vc-code>

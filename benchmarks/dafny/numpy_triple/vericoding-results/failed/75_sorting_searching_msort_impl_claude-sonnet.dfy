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
/* helper modified by LLM (iteration 5): simplified multiset lemma with explicit decreases clause */
function merge(left: seq<real>, right: seq<real>): seq<real>
  requires IsSorted(left) && IsSorted(right)
  ensures IsSorted(merge(left, right))
  ensures |merge(left, right)| == |left| + |right|
  ensures multiset(merge(left, right)) == multiset(left) + multiset(right)
  decreases |left| + |right|
{
  if |left| == 0 then right
  else if |right| == 0 then left
  else if left[0] <= right[0] then [left[0]] + merge(left[1..], right)
  else [right[0]] + merge(left, right[1..])
}

method msort_impl(a: seq<real>) returns (result: seq<real>)
  ensures |result| == |a|
  ensures IsSorted(result)
  ensures IsPermutation(a, result)
  decreases |a|
{
  if |a| <= 1 {
    result := a;
  } else {
    var mid := |a| / 2;
    var left := msort_impl(a[..mid]);
    var right := msort_impl(a[mid..]);
    result := merge(left, right);
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
/* code modified by LLM (iteration 5): direct call to implementation */
{
  result := msort_impl(a);
}
// </vc-code>

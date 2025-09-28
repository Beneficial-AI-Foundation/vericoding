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
/* helper modified by LLM (iteration 5): Fixed multiset operation types for verification */
function merge(left: seq<real>, right: seq<real>): seq<real>
  requires IsSorted(left) && IsSorted(right)
  ensures IsSorted(merge(left, right))
  ensures multiset(merge(left, right)) == multiset(left) + multiset(right)
{
  if |left| == 0 then
    right
  else if |right| == 0 then
    left
  else if left[0] <= right[0] then
    var rest := merge(left[1..], right);
    assert multiset(rest) == multiset(left[1..]) + multiset(right);
    assert multiset([left[0]] + rest) == multiset([left[0]]) + multiset(rest);
    assert multiset([left[0]] + rest) == multiset([left[0]]) + multiset(left[1..]) + multiset(right);
    assert multiset([left[0]] + rest) == multiset(left) + multiset(right);
    [left[0]] + rest
  else
    var rest := merge(left, right[1..]);
    assert multiset(rest) == multiset(left) + multiset(right[1..]);
    assert multiset([right[0]] + rest) == multiset([right[0]]) + multiset(rest);
    assert multiset([right[0]] + rest) == multiset([right[0]]) + multiset(left) + multiset(right[1..]);
    assert multiset([right[0]] + rest) == multiset(left) + multiset(right);
    [right[0]] + rest
}

method msort_helper(a: seq<real>) returns (result: seq<real>)
  ensures |result| == |a|
  ensures IsSorted(result)
  ensures IsPermutation(a, result)
{
  if |a| <= 1 {
    result := a;
  } else {
    var mid := |a| / 2;
    var left := msort_helper(a[..mid]);
    var right := msort_helper(a[mid..]);
    assert multiset(a[..mid]) + multiset(a[mid..]) == multiset(a[..mid] + a[mid..]);
    assert a[..mid] + a[mid..] == a;
    assert multiset(a[..mid] + a[mid..]) == multiset(a);
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
{
  /* code modified by LLM (iteration 5): Direct helper call with proper implementation */
  result := msort_helper(a);
}
// </vc-code>

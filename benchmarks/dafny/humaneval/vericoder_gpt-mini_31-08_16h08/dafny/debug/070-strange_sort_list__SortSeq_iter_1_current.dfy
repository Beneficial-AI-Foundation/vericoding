method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    // post-conditions-start
    ensures multiset(s) == multiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
    // post-conditions-end
{
  assume{:axiom} false;
}
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma RemoveAtPreservesMultiset<T>(xs: seq<T>, k: int)
  requires 0 <= k < |xs|
  ensures multiset(xs) == multiset(xs[..k] + xs[k+1..]) + multiset([xs[k]])
{
  // xs == xs[..k] + [xs[k]] + xs[k+1..]
  assert xs == xs[..k] + [xs[k]] + xs[k+1..];
  // multiset concatenation distributes
  assert multiset(xs) == multiset(xs[..k] + [xs[k]] + xs[k+1..]);
  assert multiset(xs[..k] + [xs[k]] + xs[k+1..]) == multiset(xs[..k]) + multiset([xs[k]]) + multiset(xs[k+1..]);
  assert multiset(xs[..k]) + multiset([xs[k]]) + multiset(xs[k+1..]) == (multiset(xs[..k]) + multiset(xs[k+1..])) + multiset([xs[k]]);
  assert (multiset(xs[..k]) + multiset(xs[k+1..])) + multiset([xs[k]]) == multiset(xs[..k] + xs[k+1..]) + multiset([xs[k]]);
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var remaining := s;
  var result := [] : seq<int>;
  // Invariants: partition of multiset, lengths add up, result sorted,
  // and last(result) <= every element of remaining (when result non-empty)
  while |remaining| > 0
    invariant multiset(s) == multiset(result) + multiset(remaining)
    invariant |result| + |remaining| == |s|
    invariant forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    invariant |result| == 0 || forall j :: 0 <= j < |remaining| ==> result[|result|-1] <= remaining[j]
    decreases |remaining|
  {
    // find index k of a minimal element in remaining
    var k := 0;
    var i := 1;
    while i < |remaining|
      invariant 0 <= k < |remaining|
      invariant 0 <= i <= |remaining|
      invariant forall j :: 0 <= j < i ==> remaining[k] <= remaining[j]
      decreases |remaining| - i
    {
      if remaining[i] < remaining[k] {
        k := i;
      }
      i := i + 1;
    }
    // k is index of a minimal element in remaining
    // Append remaining[k] to result and remove it from remaining
    result := result + [remaining[k]];
    // update remaining by removing index k
    var newRemaining := remaining[..k] + remaining[k+1..];
    // update multiset and lengths follow from lemma
    RemoveAtPreservesMultiset(remaining, k);
    remaining := newRemaining;
    // After update, invariants hold:
    // - multiset invariant: by lemma and construction
    // - length invariant: obvious
    // - sortedness: previous last <= remaining[k] (by invariant), so appending keeps sortedness;
    //   we need to show pairwise property holds for new result: prove that every previous element <= the new last
    //   Using the invariant |result|-1 old index refers to previous result before append; the loop invariants ensure this.
  }
  return result;
}
// </vc-code>


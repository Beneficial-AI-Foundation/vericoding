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

lemma AllElemsLeqFromSortedAndLast(xs: seq<int>, x: int)
  requires |xs| > 0
  requires forall i, j :: 0 <= i < j < |xs| ==> xs[i] <= xs[j]
  requires xs[|xs|-1] <= x
  ensures forall i :: 0 <= i < |xs| ==> xs[i] <= x
{
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant forall k :: 0 <= k < i ==> xs[k] <= x
  {
    if i < |xs|-1 {
      // xs[i] <= xs[|xs|-1] by sortedness
      assert xs[i] <= xs[|xs|-1];
    } else {
      // i == last, xs[i] == xs[last]
      assert xs[i] == xs[|xs|-1];
    }
    assert xs[|xs|-1] <= x;
    assert xs[i] <= x;
    i := i + 1;
  }
}

lemma RemovePreservesMin(remaining: seq<int>, k: int)
  requires 0 <= k < |remaining|
  requires forall j :: 0 <= j < |remaining| ==> remaining[k] <= remaining[j]
  ensures forall j {:trigger ((remaining[..k] + remaining[k+1..])[j])} :: 0 <= j < |remaining|-1 ==> remaining[k] <= (remaining[..k] + remaining[k+1..])[j]
{
  var newSeq := remaining[..k] + remaining[k+1..];
  var j := 0;
  while j < |newSeq|
    invariant 0 <= j <= |newSeq|
    invariant forall t :: 0 <= t < j ==> remaining[k] <= newSeq[t]
  {
    if j < k {
      assert newSeq[j] == remaining[j];
      assert remaining[k] <= newSeq[j];
    } else {
      // j >= k, then newSeq[j] == remaining[j+1]
      assert newSeq[j] == remaining[j+1];
      assert remaining[k] <= newSeq[j];
    }
    j := j + 1;
  }
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
  var result: seq<int> := [];
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
    assert forall j :: 0 <= j < |remaining| ==> remaining[k] <= remaining[j];

    // If there are previous elements in result, show they are <= remaining[k]
    if |result| > 0 {
      AllElemsLeqFromSortedAndLast(result, remaining[k]);
      assert forall i :: 0 <= i < |result| ==> result[i] <= remaining[k];
    }

    // Append remaining[k] to result
    result := result + [remaining[k]];

    // update remaining by removing index k
    var newRemaining := remaining[..k] + remaining[k+1..];
    // update multiset and lengths follow from lemma
    RemoveAtPreservesMultiset(remaining, k);
    // show that remaining[k] is <= every element of newRemaining
    RemovePreservesMin(remaining, k);
    remaining := newRemaining;

    // After update, invariants hold by the above lemmas and assertions
  }
  return result;
}
// </vc-code>


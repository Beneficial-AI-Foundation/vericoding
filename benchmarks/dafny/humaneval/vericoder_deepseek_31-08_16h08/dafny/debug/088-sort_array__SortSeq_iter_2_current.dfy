method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
{
  assume{:axiom} false;
}
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma ReverseSortedDescending(s: seq<int>)
  requires |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |s| ==> reverse(s)[i] >= reverse(s)[j]
{
  var rev := reverse(s);
  forall i, j | 0 <= i < j < |s|
    ensures rev[i] >= rev[j]
  {
    assert rev[i] == s[|s| - 1 - i];
    assert rev[j] == s[|s| - 1 - j];
    assert |s| - 1 - j < |s| - 1 - i <= |s| - 1;
    assert s[|s| - 1 - j] <= s[|s| - 1 - i];
  }
}

lemma SortedPreservesMultiset(s: seq<int>)
  ensures forall s_sorted: seq<int> {:trigger s_sorted}
    :: (|s_sorted| == |s| && multiset(s) == multiset(s_sorted)
        && forall i, j :: 0 <= i < j < |s_sorted| ==> s_sorted[i] <= s_sorted[j])
       ==> multiset(s) == multiset(s_sorted)
{
}

function method reverse_fn(s: seq<int>): seq<int>
  ensures |reverse_fn(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverse_fn(s)[k] == s[|s| - 1 - k]
{
  if |s| == 0 then []
  else [s[|s|-1]] + reverse_fn(s[0..|s|-1])
}

lemma ReverseLemma(s: seq<int>)
  ensures reverse(s) == reverse_fn(s)
{
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
  sorted := sort_array(s);
  if |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 {
    var rev := reverse(sorted);
    ReverseLemma(sorted);
    sorted := rev;
  }
}
// </vc-code>


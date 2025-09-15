// <vc-preamble>
type SortSeqState = seq<(int, int)>
function less(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  x < u || (x == u && y > v)
}
function less_eq(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  (x == u && y == v) || less(a, b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed multiset preservation proof for insertion sort */
predicate IsSorted(s: seq<(int, int)>)
{
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

lemma InsertPreservesMultiset(s: seq<(int, int)>, elem: (int, int), j: int)
  requires 0 <= j <= |s|
  ensures multiset(s[..j] + [elem] + s[j..]) == multiset(s) + multiset([elem])
{
  assert s[..j] + [elem] + s[j..] == s[..j] + ([elem] + s[j..]);
  assert multiset(s[..j] + ([elem] + s[j..])) == multiset(s[..j]) + multiset([elem] + s[j..]);
  assert multiset([elem] + s[j..]) == multiset([elem]) + multiset(s[j..]);
  assert s == s[..j] + s[j..];
  assert multiset(s) == multiset(s[..j]) + multiset(s[j..]);
}

lemma InsertPreservesSorted(s: seq<(int, int)>, elem: (int, int), j: int)
  requires IsSorted(s)
  requires 0 <= j <= |s|
  requires forall k :: 0 <= k < j ==> less_eq(s[k], elem)
  requires forall k :: j <= k < |s| ==> less_eq(elem, s[k])
  ensures IsSorted(s[..j] + [elem] + s[j..])
{
  var result := s[..j] + [elem] + s[j..];
  forall i, k | 0 <= i < k < |result|
    ensures less_eq(result[i], result[k])
  {
    if i < j && k == j {
      assert result[i] == s[i] && result[k] == elem;
    } else if i == j && k > j {
      assert result[i] == elem && result[k] == s[k-1];
    } else if i < j && k > j {
      assert result[i] == s[i] && result[k] == s[k-1];
      assert less_eq(s[i], elem) && less_eq(elem, s[k-1]);
    } else if i < j && k < j {
      assert result[i] == s[i] && result[k] == s[k];
    } else {
      assert i > j && k > j;
      assert result[i] == s[i-1] && result[k] == s[k-1];
    }
  }
}

lemma SliceEquality(s: seq<(int, int)>, i: int)
  requires 0 <= i <= |s|
  ensures s[..i] + s[i..] == s
{
}

lemma MultisetConcat(s1: seq<(int, int)>, s2: seq<(int, int)>)
  ensures multiset(s1 + s2) == multiset(s1) + multiset(s2)
{
}

method InsertionSort(s: seq<(int, int)>) returns (result: seq<(int, int)>)
  ensures IsSorted(result)
  ensures |result| == |s|
  ensures multiset(s) == multiset(result)
{
  result := [];
  for i := 0 to |s|
    invariant |result| == i
    invariant IsSorted(result)
    invariant multiset(result) == multiset(s[..i])
  {
    var elem := s[i];
    var j := 0;
    while j < |result| && less_eq(result[j], elem)
      invariant 0 <= j <= |result|
      invariant forall k :: 0 <= k < j ==> less_eq(result[k], elem)
    {
      j := j + 1;
    }
    assert forall k :: j <= k < |result| ==> less_eq(elem, result[k]);
    InsertPreservesSorted(result, elem, j);
    InsertPreservesMultiset(result, elem, j);
    var oldResult := result;
    result := result[..j] + [elem] + result[j..];
    assert multiset(result) == multiset(oldResult) + multiset([elem]);
    assert multiset(oldResult) == multiset(s[..i]);
    assert elem == s[i];
    assert multiset([elem]) == multiset([s[i]]);
    SliceEquality(s, i);
    SliceEquality(s, i+1);
    assert s[..i+1] == s[..i] + [s[i]];
    MultisetConcat(s[..i], [s[i]]);
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset([s[i]]);
    assert multiset(result) == multiset(s[..i]) + multiset([s[i]]);
    assert multiset(result) == multiset(s[..i+1]);
  }
  assert s[..|s|] == s;
  assert multiset(result) == multiset(s[..|s|]);
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): using helper sort method with proper multiset preservation */
{
  sorted := InsertionSort(s);
}
// </vc-code>

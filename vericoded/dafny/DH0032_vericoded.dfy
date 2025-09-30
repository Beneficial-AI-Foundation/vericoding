// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed lemma to work with correct sequence and added minimum finding helper */
function swap(s: seq<int>, i: int, j: int): seq<int>
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures |swap(s, i, j)| == |s|
  ensures multiset(s) == multiset(swap(s, i, j))
  ensures swap(s, i, j)[i] == s[j] && swap(s, i, j)[j] == s[i]
  ensures forall k :: 0 <= k < |s| && k != i && k != j ==> swap(s, i, j)[k] == s[k]
{
  s[i := s[j]][j := s[i]]
}

lemma SortedPreserved(s: seq<int>, i: int, minIdx: int)
  requires 0 <= i < |s| && i <= minIdx < |s|
  requires forall x, y :: 0 <= x < y < i ==> s[x] <= s[y]
  requires forall k :: i <= k < |s| ==> s[minIdx] <= s[k]
  requires forall x, y :: 0 <= x < i <= y < |s| ==> s[x] <= s[y]
  ensures forall x, y :: 0 <= x < y < i + 1 ==> swap(s, i, minIdx)[x] <= swap(s, i, minIdx)[y]
{
  var swapped := swap(s, i, minIdx);
  forall x, y | 0 <= x < y < i + 1
    ensures swapped[x] <= swapped[y]
  {
    if y == i {
      if x < i {
        assert swapped[x] == s[x];
        assert swapped[i] == s[minIdx];
        assert s[x] <= s[minIdx];
      }
    } else {
      assert x < y < i;
      assert swapped[x] == s[x];
      assert swapped[y] == s[y];
      assert s[x] <= s[y];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed sequence tracking and lemma call */
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant multiset(s) == multiset(sorted)
    invariant forall x, y :: 0 <= x < y < i ==> sorted[x] <= sorted[y]
    invariant forall x, y :: 0 <= x < i <= y < |sorted| ==> sorted[x] <= sorted[y]
  {
    var minIdx := i;
    var j := i + 1;
    while j < |sorted|
      invariant i <= minIdx < |sorted|
      invariant i <= j <= |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIdx] <= sorted[k]
    {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      SortedPreserved(sorted, i, minIdx);
      sorted := swap(sorted, i, minIdx);
    }
    i := i + 1;
  }
}
// </vc-code>

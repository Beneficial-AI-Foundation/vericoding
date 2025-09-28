// <vc-preamble>
function MultisetCount<T(==)>(s: seq<T>, x: T): nat
{
    |set i | 0 <= i < |s| && s[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): IndexOfMin returns index of a minimal element */
function IndexOfMin(s: seq<int>): int
  requires |s| > 0
  ensures 0 <= result < |s|
  ensures forall i :: 0 <= i < |s| ==> s[result] <= s[i]
  decreases |s|
{
  if |s| == 1 then 0
  else
    var k := IndexOfMin(s[1..]) + 1;
    if s[0] <= s[k] then 0 else k
}

/* helper modified by LLM (iteration 5): SortedSeq returns a sorted permutation of s */
function SortedSeq(s: seq<int>): seq<int>
  ensures |result| == |s|
  decreases |s|
{
  if |s| == 0 then []
  else
    var k := IndexOfMin(s);
    [s[k]] + SortedSeq(s[..k] + s[k+1..])
}

/* helper modified by LLM (iteration 5): SortedSeq_Properties proves sortedness and multiset equality */
lemma SortedSeq_Properties(s: seq<int>)
  ensures forall i, j :: 0 <= i < j < |SortedSeq(s)| ==> SortedSeq(s)[i] <= SortedSeq(s)[j]
  ensures forall x :: MultisetCount(SortedSeq(s), x) == MultisetCount(s, x)
  ensures |SortedSeq(s)| == |s|
  decreases |s|
{
  if |s| == 0 { return; }
  var k := IndexOfMin(s);
  var rest := s[..k] + s[k+1..];
  SortedSeq_Properties(rest);

  var res := SortedSeq(s);

  // prove sortedness
  forall i, j | 0 <= i < j < |res|
  {
    if i == 0 {
      assert res[0] == s[k];
      assert res[j] == SortedSeq(rest)[j-1];
      assert forall m | 0 <= m < |rest| :: s[k] <= rest[m];
      assert s[k] <= SortedSeq(rest)[j-1];
    } else {
      assert res[i] == SortedSeq(rest)[i-1];
      assert res[j] == SortedSeq(rest)[j-1];
      assert SortedSeq(rest)[i-1] <= SortedSeq(rest)[j-1];
    }
  }

  // prove multiset equality
  forall x
  {
    assert MultisetCount(res, x) == (if s[k] == x then 1 else 0) + MultisetCount(SortedSeq(rest), x);
    assert MultisetCount(SortedSeq(rest), x) == MultisetCount(rest, x);
    assert MultisetCount(s, x) == (if s[k] == x then 1 else 0) + MultisetCount(rest, x);
  }

  // prove length
  assert |res| == 1 + |SortedSeq(rest)|;
  assert |SortedSeq(rest)| == |rest|;
  assert |rest| == |s| - 1;
  assert |res| == |s|;
}

// </vc-helpers>

// <vc-spec>
method Sort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]) &&
        (forall x :: MultisetCount(result[..], x) == MultisetCount(a[..], x))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute SortedSeq and copy into result array */
  var s := a[..];
  var sorted := SortedSeq(s);
  SortedSeq_Properties(s);

  var n := a.Length;
  var res := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j | 0 <= j < i :: res[j] == sorted[j]
  {
    res[i] := sorted[i];
    i := i + 1;
  }
  result := res;
}

// </vc-code>

// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): defined Merge, Sorted, MultisetConcat, MultisetSingletonConcat, Merge_preserves_multiset, Merge_returns_sorted, Merge_length */
function Merge(a: seq<int>, b: seq<int>): seq<int>
  decreases |a| + |b|
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else if a[0] <= b[0] then [a[0]] + Merge(a[1..], b)
  else [b[0]] + Merge(a, b[1..])
}

predicate Sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma MultisetConcat(s: seq<int>, t: seq<int>)
  ensures multiset(s + t) == multiset(s) + multiset(t)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var x := s[0];
    var s1 := s[1..];
    MultisetConcat(s1, t);
  }
}

/* helper modified by LLM (iteration 4): singleton concat lemma to simplify multiset reasoning */
lemma MultisetSingletonConcat(x: int, s: seq<int>)
  ensures multiset([x] + s) == multiset([x]) + multiset(s)
{
  MultisetConcat([x], s);
}

/* helper modified by LLM (iteration 4): preserves multiset through Merge by induction */
lemma Merge_preserves_multiset(a: seq<int>, b: seq<int>)
  ensures multiset(Merge(a,b)) == multiset(a) + multiset(b)
  decreases |a| + |b|
{
  if |a| == 0 {
    assert Merge(a,b) == b;
    MultisetConcat(a, b);
    assert multiset(Merge(a,b)) == multiset(b);
  } else if |b| == 0 {
    assert Merge(a,b) == a;
    MultisetConcat(a, b);
    assert multiset(Merge(a,b)) == multiset(a);
  } else if a[0] <= b[0] {
    var a0 := a[0];
    var a1 := a[1..];
    Merge_preserves_multiset(a1, b);
    assert Merge(a,b) == [a0] + Merge(a1, b);
    MultisetSingletonConcat(a0, Merge(a1,b));
    assert multiset(Merge(a,b)) == multiset([a0]) + multiset(Merge(a1,b));
    assert multiset(Merge(a1,b)) == multiset(a1) + multiset(b);
    MultisetSingletonConcat(a0, a1);
    assert multiset([a0]) + multiset(a1) == multiset([a0] + a1);
    assert multiset([a0] + a1) + multiset(b) == multiset(a) + multiset(b);
    assert multiset(Merge(a,b)) == multiset(a) + multiset(b);
  } else {
    var b0 := b[0];
    var b1 := b[1..];
    Merge_preserves_multiset(a, b1);
    assert Merge(a,b) == [b0] + Merge(a, b1);
    MultisetSingletonConcat(b0, Merge(a,b1));
    assert multiset(Merge(a,b)) == multiset([b0]) + multiset(Merge(a,b1));
    assert multiset(Merge(a,b1)) == multiset(a) + multiset(b1);
    MultisetSingletonConcat(b0, b1);
    assert multiset([b0]) + multiset(b1) == multiset([b0] + b1);
    assert multiset(a) + multiset([b0] + b1) == multiset(a) + multiset(b);
    assert multiset(Merge(a,b)) == multiset(a) + multiset(b);
  }
}

lemma Merge_returns_sorted(a: seq<int>, b: seq<int>)
  requires Sorted(a) && Sorted(b)
  ensures Sorted(Merge(a,b))
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if a[0] <= b[0] {
    var a0 := a[0];
    var a1 := a[1..];
    Merge_returns_sorted(a1, b);
  } else {
    var b0 := b[0];
    var b1 := b[1..];
    Merge_returns_sorted(a, b1);
  }
}

lemma Merge_length(a: seq<int>, b: seq<int>)
  ensures |Merge(a,b)| == |a| + |b|
  decreases |a| + |b|
{
  if |a| == 0 {
  } else if |b| == 0 {
  } else if a[0] <= b[0] {
    Merge_length(a[1..], b);
  } else {
    Merge_length(a, b[1..]);
  }
}

// </vc-helpers>

// <vc-spec>
method MergeSort(list: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |list| &&
        (forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]) &&
        multiset(result) == multiset(list)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): implement MergeSort using Merge and helper lemmas */
{
  if |list| <= 1 {
    result := list;
    return;
  }
  var mid := |list| / 2;
  var left := list[..mid];
  var right := list[mid..];
  var lres := MergeSort(left);
  var rres := MergeSort(right);
  result := Merge(lres, rres);
  // lengths and sortedness
  Merge_length(lres, rres);
  Merge_returns_sorted(lres, rres);
  // multisets: use helper lemmas and recursive postconditions
  Merge_preserves_multiset(lres, rres);
  assert multiset(result) == multiset(lres) + multiset(rres);
  // postconditions of recursive calls
  assert multiset(lres) == multiset(left);
  assert multiset(rres) == multiset(right);
  // concat left and right equals original list
  MultisetConcat(left, right);
  assert multiset(left) + multiset(right) == multiset(left + right);
  assert left + right == list;
  assert multiset(left + right) == multiset(list);
  // conclude multiset(result) == multiset(list)
  assert multiset(result) == multiset(list);
}

// </vc-code>

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
/* helper modified by LLM (iteration 3): Fixed partition multiset invariant and sorted_concatenation lemma proof */
predicate is_sorted(s: SortSeqState)
{
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

method partition(s: SortSeqState, pivot: (int, int)) returns (left: SortSeqState, equal: SortSeqState, right: SortSeqState)
  ensures multiset(s) == multiset(left) + multiset(equal) + multiset(right)
  ensures forall x :: x in left ==> less(x, pivot)
  ensures forall x :: x in equal ==> x == pivot
  ensures forall x :: x in right ==> less(pivot, x)
{
  left := [];
  equal := [];
  right := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant multiset(left) + multiset(equal) + multiset(right) == multiset(s[..i])
    invariant forall x :: x in left ==> less(x, pivot)
    invariant forall x :: x in equal ==> x == pivot
    invariant forall x :: x in right ==> less(pivot, x)
  {
    if less(s[i], pivot) {
      left := left + [s[i]];
    } else if s[i] == pivot {
      equal := equal + [s[i]];
    } else {
      right := right + [s[i]];
    }
    i := i + 1;
  }
  assert s[..i] == s;
}

lemma sorted_concatenation(left: SortSeqState, equal: SortSeqState, right: SortSeqState, pivot: (int, int))
  requires is_sorted(left)
  requires is_sorted(right)
  requires forall x :: x in left ==> less(x, pivot)
  requires forall x :: x in equal ==> x == pivot
  requires forall x :: x in right ==> less(pivot, x)
  ensures is_sorted(left + equal + right)
{
  var result := left + equal + right;
  forall i, j | 0 <= i < j < |result|
    ensures less_eq(result[i], result[j])
  {
    if i < |left| && j < |left| {
      assert result[i] == left[i];
      assert result[j] == left[j];
      assert less_eq(result[i], result[j]);
    } else if i < |left| && j < |left| + |equal| {
      var idx := j - |left|;
      assert result[i] == left[i];
      assert result[j] == equal[idx];
      assert equal[idx] == pivot;
      assert less(result[i], pivot);
      assert less_eq(result[i], result[j]);
    } else if i < |left| && j >= |left| + |equal| {
      var idx := j - |left| - |equal|;
      assert result[i] == left[i];
      assert result[j] == right[idx];
      assert less(result[i], pivot);
      assert less(pivot, result[j]);
      assert less_eq(result[i], result[j]);
    } else if i < |left| + |equal| && j < |left| + |equal| {
      var idx_i := i - |left|;
      var idx_j := j - |left|;
      assert result[i] == equal[idx_i];
      assert result[j] == equal[idx_j];
      assert equal[idx_i] == pivot;
      assert equal[idx_j] == pivot;
      assert result[i] == pivot && result[j] == pivot;
      assert less_eq(result[i], result[j]);
    } else if i < |left| + |equal| && j >= |left| + |equal| {
      var idx_i := i - |left|;
      var idx_j := j - |left| - |equal|;
      assert result[i] == equal[idx_i];
      assert equal[idx_i] == pivot;
      assert result[j] == right[idx_j];
      assert less(pivot, result[j]);
      assert less_eq(result[i], result[j]);
    } else {
      assert i >= |left| + |equal| && j >= |left| + |equal|;
      var idx_i := i - |left| - |equal|;
      var idx_j := j - |left| - |equal|;
      assert result[i] == right[idx_i];
      assert result[j] == right[idx_j];
      assert less_eq(result[i], result[j]);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Moved decreases clause to correct position before method body */
  if |s| <= 1 {
    sorted := s;
  } else {
    var pivot := s[|s| / 2];
    var left, equal, right := partition(s, pivot);
    var sortedLeft := SortSeq(left);
    var sortedRight := SortSeq(right);
    sorted := sortedLeft + equal + sortedRight;
    assert is_sorted(sortedLeft);
    assert is_sorted(sortedRight);
    assert forall x :: x in sortedLeft ==> x in left;
    assert forall x :: x in sortedRight ==> x in right;
    sorted_concatenation(sortedLeft, equal, sortedRight, pivot);
    assert is_sorted(sorted);
  }
}
// </vc-code>

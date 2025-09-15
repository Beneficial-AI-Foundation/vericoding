// <vc-preamble>
function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added sequence extension lemma to properly establish multiset equality */
predicate is_sorted_by_digits(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> digits_sum(s[i]) <= digits_sum(s[j])
}

lemma insert_sorted_preserves_multiset(s: seq<int>, x: int, pos: int)
  requires 0 <= pos <= |s|
  ensures multiset(s[..pos] + [x] + s[pos..]) == multiset(s) + multiset{x}
{
  assert s[..pos] + [x] + s[pos..] == s[..pos] + ([x] + s[pos..]);
  assert multiset(s[..pos] + ([x] + s[pos..])) == multiset(s[..pos]) + multiset([x] + s[pos..]);
  assert multiset([x] + s[pos..]) == multiset{x} + multiset(s[pos..]);
  assert s == s[..pos] + s[pos..];
  assert multiset(s) == multiset(s[..pos]) + multiset(s[pos..]);
}

lemma insert_sorted_maintains_order(s: seq<int>, x: int, pos: int)
  requires 0 <= pos <= |s|
  requires is_sorted_by_digits(s)
  requires pos == 0 || digits_sum(s[pos-1]) <= digits_sum(x)
  requires pos == |s| || digits_sum(x) <= digits_sum(s[pos])
  ensures is_sorted_by_digits(s[..pos] + [x] + s[pos..])
{
  var result := s[..pos] + [x] + s[pos..];
  forall i, j | 0 <= i < j < |result| 
    ensures digits_sum(result[i]) <= digits_sum(result[j])
  {
    if i < pos && j == pos {
      assert result[j] == x;
      assert result[i] == s[i];
      assert digits_sum(s[i]) <= digits_sum(x);
    } else if i == pos && j > pos {
      assert result[i] == x;
      assert result[j] == s[j-1];
      assert digits_sum(x) <= digits_sum(s[j-1]);
    } else if i < pos && j > pos {
      assert result[i] == s[i];
      assert result[j] == s[j-1];
      assert digits_sum(s[i]) <= digits_sum(s[j-1]);
    } else if i < pos && j < pos {
      assert result[i] == s[i];
      assert result[j] == s[j];
      assert digits_sum(s[i]) <= digits_sum(s[j]);
    } else {
      assert pos < i < j;
      assert result[i] == s[i-1];
      assert result[j] == s[j-1];
      assert digits_sum(s[i-1]) <= digits_sum(s[j-1]);
    }
  }
}

lemma multiset_slice_extension(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]}
{
  assert s[..i+1] == s[..i] + [s[i]];
  assert multiset(s[..i] + [s[i]]) == multiset(s[..i]) + multiset([s[i]]);
  assert multiset([s[i]]) == multiset{s[i]};
}

lemma sequence_equals_prefix(s: seq<int>)
  ensures s[..|s|] == s
{
}

lemma multiset_prefix_complete(s: seq<int>)
  ensures multiset(s[..|s|]) == multiset(s)
{
  sequence_equals_prefix(s);
}
// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added final multiset equality proof after loop completion */
{
  sorted := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant is_sorted_by_digits(sorted)
    invariant multiset(sorted) == multiset(s[..i])
  {
    var x := s[i];
    var pos := 0;
    while pos < |sorted| && digits_sum(sorted[pos]) <= digits_sum(x)
      invariant 0 <= pos <= |sorted|
      invariant forall k :: 0 <= k < pos ==> digits_sum(sorted[k]) <= digits_sum(x)
    {
      pos := pos + 1;
    }
    var old_sorted := sorted;
    sorted := sorted[..pos] + [x] + sorted[pos..];
    insert_sorted_preserves_multiset(old_sorted, x, pos);
    insert_sorted_maintains_order(old_sorted, x, pos);
    multiset_slice_extension(s, i);
    assert multiset(sorted) == multiset(old_sorted) + multiset{x};
    assert multiset(old_sorted) == multiset(s[..i]);
    assert multiset{x} == multiset{s[i]};
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]};
  }
  multiset_prefix_complete(s);
  assert multiset(s[..|s|]) == multiset(s);
  assert multiset(sorted) == multiset(s[..|s|]);
}
// </vc-code>

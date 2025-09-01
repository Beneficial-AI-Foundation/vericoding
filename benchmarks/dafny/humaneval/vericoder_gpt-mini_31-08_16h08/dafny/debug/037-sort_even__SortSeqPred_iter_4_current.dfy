method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function CountTrue(p: seq<bool>, n: int): int
  requires 0 <= n <= |p|
  decreases n
  ensures 0 <= CountTrue(p, n) <= n
{
  if n == 0 then 0 else CountTrue(p, n - 1) + (if p[n - 1] then 1 else 0)
}

lemma CountTrue_succ(p: seq<bool>, i: int)
  requires 0 <= i < |p|
  ensures CountTrue(p, i + 1) == CountTrue(p, i) + (if p[i] then 1 else 0)
{
  // By definition of CountTrue
  if i + 1 == 0 {
    // impossible
  } else {
    // unfolding the definition yields the desired equality
    assert CountTrue(p, i + 1) == CountTrue(p, i) + (if p[i] then 1 else 0);
  }
}

lemma CountTrueMonotone(p: seq<bool>, m: int, n: int)
  requires 0 <= m <= n <= |p|
  ensures CountTrue(p, m) <= CountTrue(p, n)
  decreases n - m
{
  if m == n {
    return;
  }
  // n > m, so n >= 1
  CountTrueMonotone(p, m, n - 1);
  assert CountTrue(p, n) == CountTrue(p, n - 1) + (if p[n - 1] then 1 else 0);
  if p[n - 1] {
    assert CountTrue(p, n - 1) < CountTrue(p, n);
    assert CountTrue(p, m) <= CountTrue(p, n);
  } else {
    assert CountTrue(p, n - 1) == CountTrue(p, n);
    assert CountTrue(p, m) <= CountTrue(p, n);
  }
}

lemma SeqFilterLen(s: seq<int>, p: seq<bool>, n: int)
  requires |s| == |p|
  requires 0 <= n <= |s|
  ensures |(seq i | 0 <= i < n && p[i] :: s[i])| == CountTrue(p, n)
  decreases n
{
  if n == 0 {
    // both sides are 0
    assert |(seq i | 0 <= i < 0 && p[i] :: s[i])| == 0;
    assert CountTrue(p, 0) == 0;
    return;
  }
  SeqFilterLen(s, p, n - 1);
  CountTrue_succ(p, n - 1);
  if p[n - 1] {
    // When p[n-1] is true, the comprehension for n adds one more element compared to n-1
    assert |(seq i | 0 <= i < n && p[i] :: s[i])| == |(seq i | 0 <= i < n - 1 && p[i] :: s[i])| + 1;
    assert CountTrue(p, n) == CountTrue(p, n - 1) + 1;
    assert |(seq i | 0 <= i < n && p[i] :: s[i])| == CountTrue(p, n);
  } else {
    // When p[n-1] is false, the comprehension for n has the same length as for n-1
    assert |(seq i | 0 <= i < n && p[i] :: s[i])| == |(seq i | 0 <= i < n - 1 && p[i] :: s[i])|;
    assert CountTrue(p, n) == CountTrue(p, n - 1);
    assert |(seq i | 0 <= i < n && p[i] :: s[i])| == CountTrue(p, n);
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  // Filter s according to predicate p
  var sFilt := seq i | 0 <= i < |s| && p[i] :: s[i];
  var sortedFilt := SortSeq(sFilt);

  // Relate length of the filtered sequence to CountTrue
  SeqFilterLen(s, p, |s|);

  // Build result in a mutable array for easy updates
  var arr := new int[|s|];
  var i := 0;
  var pos := 0;
  // Invariant: pos == CountTrue(p, i), and arr[0..i) has been set appropriately
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= pos <= |sortedFilt|
    invariant pos == CountTrue(p, i)
    invariant forall k :: 0 <= k < i && !p[k] ==> arr[k] == s[k]
    invariant forall k :: 0 <= k < i && p[k] ==> arr[k] == sortedFilt[CountTrue(p, k + 1) - 1]
  {
    if p[i] {
      // Need to ensure pos < |sortedFilt|
      // pos == CountTrue(p,i) and CountTrue(p,i+1) == pos + 1
      CountTrue_succ(p, i);
      // CountTrue(p, i+1) <= CountTrue(p, |s|)
      CountTrueMonotone(p, i + 1, |s|);
      // And CountTrue(p, |s|) == |sFilt| and |sortedFilt| == |sFilt|
      assert CountTrue(p, |s|) == |sFilt|;
      assert |sortedFilt| == |sFilt|;
      assert pos + 1 <= |sortedFilt|;
      // hence pos < |sortedFilt|
      arr[i] := sortedFilt[pos];
      pos := pos + 1;
    } else {
      arr[i] := s[i];
    }
    i := i + 1;
  }

  sorted := arr[..];

  // Post-checks to help the verifier
  // Lengths
  assert |sorted| == |s|;

  // For non-selected positions, value preserved
  assert forall k :: 0 <= k < |s| && !p[k] ==> sorted[k] == s[k];

  // For selected positions, values come from sortedFilt with monotonically increasing indices
  assert forall i1, i2 :: 0 <= i1 < i2 < |s| && p[i1] && p[i2] ==>
    let idx1 := CountTrue(p, i1 + 1) - 1 in
    let idx2 := CountTrue(p, i2 + 1) - 1 in
      0 <= idx1 < |sortedFilt| && 0 <= idx2 < |sortedFilt| && idx1 < idx2 && sorted[i1] == sortedFilt[idx1] && sorted[i2] == sortedFilt[idx2];

  // Use sortedness of sortedFilt to conclude ordering on selected positions
  assert forall i1, i2 :: 0 <= i1 < i2 < |s| && p[i1] && p[i2] ==> sorted[i1] <= sorted[i2] by {
    // By previous assertion we have idx1 < idx2 and sorted[i*] == sortedFilt[idx*]
    var idx1 := CountTrue(p, i1 + 1) - 1;
    var idx2 := CountTrue(p, i2 + 1) - 1;
    assert 0 <= idx1 < |sortedFilt|;
    assert 0 <= idx2 < |sortedFilt|;
    assert idx1 < idx2;
    assert sorted[i1] == sortedFilt[idx1];
    assert sorted[i2] == sortedFilt[idx2];
    // sortedFilt is sorted
    assert forall a, b :: 0 <= a < b < |sortedFilt| ==> sortedFilt[a] <= sortedFilt[b];
    assert sortedFilt[idx1] <= sortedFilt[idx2];
  }

  // Multiset: multiset(sorted) == multiset(s)
  // multiset(sorted) consists of elements from non-selected positions (same as s) and selected positions (sortedFilt),
  // and multiset(sortedFilt) == multiset(sFilt), and sFilt together with non-selected positions form s.
  assert multiset(sorted) == multiset(s);
}
// </vc-code>


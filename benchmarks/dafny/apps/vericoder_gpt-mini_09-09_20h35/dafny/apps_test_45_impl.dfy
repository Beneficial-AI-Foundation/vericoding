predicate ValidInput(n: int, k: int)
{
    n > 0 && k > 0
}

predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] > 0
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidSequence(s: seq<int>, n: int, k: int)
{
    |s| == k && AllPositive(s) && IsStrictlyIncreasing(s) && sum(s) == n
}

predicate IsPossible(n: int, k: int)
{
    k * (k + 1) / 2 <= n
}

// <vc-helpers>
lemma SumAppend(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
  decreases |s|
{
  if |s| == 0 {
    // sum([x]) == x and sum([]) == 0
    assert sum([x]) == x;
    assert sum([]) == 0;
  } else {
    // unfold definitions
    assert sum(s + [x]) == s[0] + sum(s[1..] + [x]);
    SumAppend(s[1..], x);
    assert sum(s[1..] + [x]) == sum(s[1..]) + x;
    assert sum(s + [x]) == s[0] + (sum(s[1..]) + x);
    assert sum(s) == s[0] + sum(s[1..]);
  }
  assert sum(s + [x]) == sum(s) + x;
}

lemma SumStart(k: int, s: seq<int>, start: int)
  requires k >= 0
  requires |s| == k
  requires forall i :: 0 <= i < k ==> s[i] == i + start
  ensures sum(s) == k * start + k * (k - 1) / 2
  decreases k
{
  if k == 0 {
    assert sum(s) == 0;
  } else {
    // sum(s) = start + sum(s[1..])
    assert sum(s) == s[0] + sum(s[1..]);
    SumStart(k - 1, s[1..], start + 1);
    // from recursive call
    assert sum(s[1..]) == (k - 1) * (start + 1) + (k - 1) * (k - 2) / 2;
    // combine
    assert sum(s) == start + ((k - 1) * (start + 1) + (k - 1) * (k - 2) / 2);
    assert start + ((k - 1) * (start + 1) + (k - 1) * (k - 2) / 2) == k * start + k * (k - 1) / 2;
    assert sum(s) == k * start + k * (k - 1) / 2;
  }
}

lemma AppendPreservesIndices(prev: seq<int>, x: int)
  ensures forall j :: 0 <= j < |prev| ==> (prev + [x])[j] == prev[j]
  decreases |prev|
{
  if |prev| == 0 {
  } else {
    AppendPreservesIndices(prev[1..], x);
  }
}

lemma AppendLast(prev: seq<int>, x: int)
  ensures (prev + [x])[|prev|] == x
  decreases |prev|
{
  if |prev| == 0 {
  } else {
    AppendLast(prev[1..], x);
  }
}

lemma SlicePrefixIndex(s: seq<int>, m: int)
  requires 0 <= m <= |s|
  ensures forall j :: 0 <= j < m ==> (s[..m])[j] == s[j]
  decreases m
{
  if m == 0 { }
  else {
    SlicePrefixIndex(s, m - 1);
    assert (s[..m])[m-1] == s[m-1];
  }
}

lemma SlicePreservePrefix(s: seq<int>, m: int)
  requires 0 <= m <= |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == j + 1
  ensures forall j :: 0 <= j < m ==> (s[..m])[j] == j + 1
  decreases m
{
  if m == 0 { }
  else {
    SlicePreservePrefix(s, m - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures (|result| == 1 && result[0] == -1) || 
            (ValidSequence(result, n, k))
    ensures (|result| == 1 && result[0] == -1) <==> !IsPossible(n, k)
// </vc-spec>
// <vc-code>
{
  if !IsPossible(n, k) {
    return [-1];
  }

  var res: seq<int> := [];
  var ssum: int := 0;
  var i := 1;
  while i <= k
    invariant 1 <= i <= k + 1
    invariant |res| == i - 1
    invariant sum(res) == ssum
    invariant forall j :: 0 <= j < |res| ==> res[j] == j + 1
  {
    var prev := res;
    res := prev + [i];
    ssum := ssum + i;
    SumAppend(prev, i);
    AppendPreservesIndices(prev, i);
    AppendLast(prev, i);
    // prove the element property for the new res
    assert forall j :: 0 <= j < |prev| ==> res[j] == j + 1;
    assert res[|prev|] == i;
    assert i == |prev| + 1;
    assert forall j :: 0 <= j < |res| ==> res[j] == j + 1;
    // sum(res) == ssum follows from SumAppend(prev, i) and previous invariant
    assert sum(res) == ssum;
    i := i + 1;
  }

  // Now res == [1,2,...,k] and ssum == sum(res) == k*(k+1)/2
  SumStart(k, res, 1);
  assert ssum == k * (k + 1) / 2;

  var rem := n - ssum;
  // From IsPossible and the above equality, rem >= 0
  assert rem >= 0;

  if k == 0 {
    // should not happen due to ValidInput, but handle defensively
    return [-1];
  }

  var pref := res[..|res|-1];
  var last := res[|res|-1];
  var newLast := last + rem;
  // build the final sequence
  var final := pref + [newLast];
  // relate sums
  // prove res == pref + [last]
  SlicePrefixIndex(res, |res|-1);
  assert |pref + [last]| == |res|;
  assert forall j :: 0 <= j < |pref| ==> (pref + [last])[j] == res[j];
  assert (pref + [last])[|pref|] == res[|pref|];
  assert pref + [last] == res;

  SumAppend(pref, last);
  assert sum(res) == sum(pref) + last;
  SumAppend(pref, newLast);
  assert sum(final) == sum(pref) + newLast;
  assert sum(final) == sum(res) - last + newLast;
  assert sum(final) == ssum + rem;
  assert sum(final) == n;

  // prove strictly increasing:
  // use preservation lemmas to expose element equalities
  SlicePreservePrefix(res, |res|-1);
  AppendPreservesIndices(pref, newLast);
  AppendLast(pref, newLast);
  assert forall j :: 0 <= j < |final| - 1 ==> final[j] < final[j+1];
  // prove all positive
  assert forall j :: 0 <= j < |final| ==> final[j] > 0;
  return final;
}
// </vc-code>


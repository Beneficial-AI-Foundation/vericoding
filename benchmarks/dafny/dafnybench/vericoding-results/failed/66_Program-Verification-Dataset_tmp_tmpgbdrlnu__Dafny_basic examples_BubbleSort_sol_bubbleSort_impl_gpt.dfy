predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{
  sorted_between (a, 0, a.Length)
}

// <vc-helpers>
predicate sorted_seq(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function ins(x: int, s: seq<int>): seq<int>
  requires sorted_seq(s)
  decreases |s|
  ensures sorted_seq(ins(x, s))
  ensures multiset(ins(x, s)) == multiset(s) + multiset([x])
  ensures |ins(x, s)| == |s| + 1
{
  if |s| == 0 then
    [x]
  else if x <= s[0] then
    [x] + s
  else
    [s[0]] + ins(x, s[1..])
}

function sortSeq(s: seq<int>): seq<int>
  decreases |s|
  ensures sorted_seq(sortSeq(s))
  ensures multiset(sortSeq(s)) == multiset(s)
  ensures |sortSeq(s)| == |s|
{
  if |s| == 0 then s
  else ins(s[0], sortSeq(s[1..]))
}

lemma sorted_seq_preserved_by_equality(s: seq<int>, t: seq<int>)
  requires s == t
  ensures sorted_seq(s) ==> sorted_seq(t)
  ensures sorted_seq(t) ==> sorted_seq(s)
{
}

lemma seq_sorted_implies_sorted_array(a: array<int>)
  requires a != null
  requires sorted_seq(a[..])
  ensures sorted(a)
  reads a
{
  assert forall i, j | 0 <= i < j < a.Length ==> a[i] <= a[j] {
    assert 0 <= i < j < |a[..]|
    assert a[..][i] <= a[..][j]
    assert a[..][i] == a[i]
    assert a[..][j] == a[j]
  }
}
// </vc-helpers>

// <vc-spec>
method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
// </vc-spec>
// <vc-code>
{
  ghost var s0 := a[..]
  ghost var t := sortSeq(s0)
  assert |t| == |s0|
  assert |s0| == a.Length
  var i := 0
  while i < a.Length
    invariant a != null
    invariant 0 <= i <= a.Length
    invariant |t| == a.Length
    invariant a[..i] == t[..i]
    decreases a.Length - i
  {
    a[i] := t[i]
    i := i + 1
  }
  assert i == a.Length
  assert a[..i] == a
// </vc-code>


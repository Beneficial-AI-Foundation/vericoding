function UnnecessaryCardsCount(sorted: seq<int>, k: int): int
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  requires forall i :: 0 <= i < |sorted| ==> sorted[i] >= 1
  requires k >= 1
{
  if |sorted| == 0 then 0
  else
    UnnecessaryCardsCountHelper(sorted, k, 0, 0, 0)
}

function UnnecessaryCardsCountHelper(sorted: seq<int>, k: int, temp: int, ans: int, i: int): int
  requires forall x, y :: 0 <= x < y < |sorted| ==> sorted[x] >= sorted[y]
  requires forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1
  requires k >= 1
  requires 0 <= i <= |sorted|
  requires temp >= 0
  requires ans >= 0
  decreases |sorted| - i
{
  if i >= |sorted| then ans
  else
    var x := sorted[i];
    if temp + x < k then
      UnnecessaryCardsCountHelper(sorted, k, temp + x, ans + 1, i + 1)
    else
      UnnecessaryCardsCountHelper(sorted, k, 0, 0, i + 1)
}

// <vc-helpers>
method insertDescending(s: seq<int>, elem: int) returns (r: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
  requires elem >= 1
  ensures |r| == |s| + 1
  ensures multiset(r) == multiset(s + [elem])
  ensures forall i, j :: 0 <= i < j < |r| ==> r[i] >= r[j]
  ensures forall i :: 0 <= i < |r| ==> r[i] >= 1
{
  var i := 0;
  while i < |s| && s[i] >= elem
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> s[k] >= elem
  {
    i := i + 1;
  }
  r := s[..i] + [elem] + s[i..];
}

method sortSeqDescending(a: seq<int>) returns (r: seq<int>)
  requires forall i :: 0 <= i < |a| ==> a[i] >= 1
  ensures |r| == |a|
  ensures multiset(r) == multiset(a)
  ensures forall i, j :: 0 <= i < j < |r| ==> r[i] >= r[j]
  ensures forall i :: 0 <= i < |r| ==> r[i] >= 1
{
  r := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |r| == i
    invariant multiset(r) == multiset(a[..i])
    invariant forall k :: 0 <= k < |r| ==> r[k] >= 1
    invariant forall p, q :: 0 <= p < q < |r| ==> r[p] >= r[q]
  {
    r := insertDescending(r, a[i]);
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (result: int)
  requires n >= 1
  requires k >= 1
  requires |a| == n
  requires forall i :: 0 <= i < |a| ==> a[i] >= 1
  ensures result >= 0
  ensures result <= n
  ensures exists sorted :: 
    |sorted| == |a| &&
    multiset(sorted) == multiset(a) &&
    (forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]) &&
    (forall i :: 0 <= i < |sorted| ==> sorted[i] >= 1) &&
    result == UnnecessaryCardsCount(sorted, k)
// </vc-spec>
// <vc-code>
{
  var sorted := sortSeqDescending(a);
  result := UnnecessaryCardsCount(sorted, k);
}
// </vc-code>


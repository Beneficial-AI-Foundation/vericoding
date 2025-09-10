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
function MultisetsEqual<T>(s1: seq<T>, s2: seq<T>): bool
  reads s1, s2
{
  multiset(s1) == multiset(s2)
}

function SortDescending(a: seq<int>): seq<int>
  ensures |SortDescending(a)| == |a|
  ensures MultisetsEqual(SortDescending(a), a)
  ensures forall i, j :: 0 <= i < j < |SortDescending(a)| ==> SortDescending(a)[i] >= SortDescending(a)[j]
  ensures forall i :: 0 <= i < |a| ==> a[i] in multiset(SortDescending(a))
  ensures forall i :: 0 <= i < |SortDescending(a)| ==> SortDescending(a)[i] in multiset(a)
{
  if |a| <= 1 then a
  else
    var pivot := a[0];
    var lessEq: seq<int> := [];
    var greater: seq<int> := [];
    for i := 1 to |a|-1
      invariant 0 <= i <= |a|
      invariant pivot == a[0]
      invariant forall x :: x in multiset(lessEq) ==> x <= pivot
      invariant forall x :: x in multiset(greater) ==> x > pivot
      invariant multiset(lessEq) + multiset(greater) + multiset([pivot]) + multiset(a[i..|a|]) == multiset(a)
      decreases |a| - i
    {
      if a[i] <= pivot then
        lessEq := lessEq + [a[i]];
      else
        greater := greater + [a[i]];
    }
    SortDescending(greater) + [pivot] + SortDescending(lessEq)
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
    var sorted_a := SortDescending(a);
    result := UnnecessaryCardsCount(sorted_a, k);
}
// </vc-code>


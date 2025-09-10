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
function PickMaxIndex(s: seq<int>): int
  requires |s| > 0
  ensures 0 <= result < |s|
  ensures forall j :: 0 <= j < |s| ==> s[result] >= s[j]
  decreases |s|
{
  if |s| == 1 then 0
  else
    var r := PickMaxIndex(s[1..]);
    if s[0] >= s[1 + r] then 0 else 1 + r
}

function RemoveAt(s: seq<int>, m: int): seq<int>
  requires 0 <= m < |s|
{
  s[..m] + s[m+1..]
}

function method Sort(s: seq<int>): seq<int>
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures |result| == |s|
  ensures multiset(result) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] >= result[j]
  ensures forall i :: 0 <= i < |result| ==> result[i] >= 1
  decreases |s|
{
  if |s| == 0 then
    []
  else
    var m := PickMaxIndex(s);
    [s[m]] + Sort(RemoveAt(s, m))
}

lemma SortPreservesMultiset(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures multiset(Sort(s)) == multiset(s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var m := PickMaxIndex(s);
    var rest := RemoveAt(s, m);
    SortPreservesMultiset(rest);
  }
}

lemma SortIsNonincreasing(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures forall i, j :: 0 <= i < j < |Sort(s)| ==> Sort(s)[i] >= Sort(s)[j]
  decreases |s|
{
  if |s| == 0 {
  } else {
    var m := PickMaxIndex(s);
    var rest := RemoveAt(s, m);
    SortIsNonincreasing(rest);
  }
}

lemma SortHasSameLengthAndPositives(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures |Sort(s)| == |s|
  ensures forall i :: 0 <= i < |Sort(s)| ==> Sort(s)[i] >= 1
  decreases |s|
{
  if |s| == 0 {
  } else {
    var m := PickMaxIndex(s);
    var rest := RemoveAt(s, m);
    SortHasSameLengthAndPositives(rest);
  }
}

lemma UnnecessaryCardsCountHelperBound(sorted: seq<int>, k: int, temp: int, ans: int, i: int)
  requires forall x, y :: 0 <= x < y < |sorted| ==> sorted[x] >= sorted[y]
  requires forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1
  requires k >= 1
  requires 0 <= i <= |sorted|
  requires temp >= 0
  requires ans >= 0
  ensures 0 <= UnnecessaryCardsCountHelper(sorted, k, temp, ans, i) <= ans + (|sorted| - i)
  decreases |sorted| - i
{
  if i >= |sorted| {
  } else {
    var x := sorted[i];
    if temp + x < k {
      UnnecessaryCardsCountHelperBound(sorted, k, temp + x, ans + 1, i + 1);
    } else {
      UnnecessaryCardsCountHelperBound(sorted, k, 0, 0, i + 1);
    }
  }
}

lemma UnnecessaryCardsCountBounds(sorted: seq<int>, k: int)
  requires forall x, y :: 0 <= x < y < |sorted| ==> sorted[x] >= sorted[y]
  requires forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1
  requires k >= 1
  ensures 0 <= UnnecessaryCardsCount(sorted, k) <= |sorted|
{
  UnnecessaryCardsCountHelperBound(sorted, k, 0, 0, 0);
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
  ghost var sorted := Sort(a);
  result := UnnecessaryCardsCount(sorted, k);
}
// </vc-code>


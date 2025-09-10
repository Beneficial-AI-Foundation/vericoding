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
method SortDescending(a: seq<int>) returns (sorted: seq<int>)
  requires forall i :: 0 <= i < |a| ==> a[i] >= 1
  ensures |sorted| == |a|
  ensures multiset(sorted) == multiset(a)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] >= 1
{
  sorted := a;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |a|
    invariant multiset(sorted) == multiset(a)
    invariant forall k :: 0 <= k < |sorted| ==> sorted[k] >= 1
    invariant forall j, k :: 0 <= j < k < i ==> sorted[j] >= sorted[k]
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> sorted[j] >= sorted[k]
  {
    var j := i + 1;
    var maxIndex := i;
    while j < |sorted|
      invariant i < j <= |sorted|
      invariant i <= maxIndex < j
      invariant forall k :: i <= k < j ==> sorted[maxIndex] >= sorted[k]
    {
      if sorted[j] > sorted[maxIndex] {
        maxIndex := j;
      }
      j := j + 1;
    }
    
    if maxIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[maxIndex]][maxIndex := temp];
    }
    
    i := i + 1;
  }
}

lemma UnnecessaryCardsCountBounds(sorted: seq<int>, k: int)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  requires forall i :: 0 <= i < |sorted| ==> sorted[i] >= 1
  requires k >= 1
  ensures 0 <= UnnecessaryCardsCount(sorted, k) <= |sorted|
{
  if |sorted| == 0 {
    assert UnnecessaryCardsCount(sorted, k) == 0;
  } else {
    UnnecessaryCardsCountHelperBounds(sorted, k, 0, 0, 0);
  }
}

lemma UnnecessaryCardsCountHelperBounds(sorted: seq<int>, k: int, temp: int, ans: int, i: int)
  requires forall x, y :: 0 <= x < y < |sorted| ==> sorted[x] >= sorted[y]
  requires forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1
  requires k >= 1
  requires 0 <= i <= |sorted|
  requires temp >= 0
  requires ans >= 0
  requires ans <= i
  decreases |sorted| - i
  ensures 0 <= UnnecessaryCardsCountHelper(sorted, k, temp, ans, i) <= |sorted|
{
  if i >= |sorted| {
    assert UnnecessaryCardsCountHelper(sorted, k, temp, ans, i) == ans;
    assert ans <= i <= |sorted|;
  } else {
    var x := sorted[i];
    if temp + x < k {
      assert ans + 1 <= i + 1;
      UnnecessaryCardsCountHelperBounds(sorted, k, temp + x, ans + 1, i + 1);
    } else {
      assert 0 <= i + 1;
      UnnecessaryCardsCountHelperBounds(sorted, k, 0, 0, i + 1);
    }
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
  var sorted := SortDescending(a);
  UnnecessaryCardsCountBounds(sorted, k);
  result := UnnecessaryCardsCount(sorted, k);
}
// </vc-code>


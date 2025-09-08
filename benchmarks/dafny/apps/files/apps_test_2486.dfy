Given N cards with positive integers, determine how many cards are "unnecessary."
A subset of cards is "good" if the sum of its numbers is at least K.
A card is "unnecessary" if for every good subset containing this card, 
removing the card from that subset still results in a good subset.
Count the number of unnecessary cards.

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
      invariant forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1
      invariant forall x, y :: 0 <= x < y < i ==> sorted[x] >= sorted[y]
      invariant forall x :: 0 <= x < i ==> forall y :: i <= y < |sorted| ==> sorted[x] >= sorted[y]
    {
        var maxIdx := i;
        var j := i + 1;
        while j < |sorted|
          invariant i < j <= |sorted|
          invariant i <= maxIdx < |sorted|
          invariant forall x :: i <= x < j ==> sorted[maxIdx] >= sorted[x]
          invariant |sorted| == |a|
          invariant multiset(sorted) == multiset(a)
          invariant forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1
          invariant forall x, y :: 0 <= x < y < i ==> sorted[x] >= sorted[y]
          invariant forall x :: 0 <= x < i ==> forall y :: i <= y < |sorted| ==> sorted[x] >= sorted[y]
        {
            if sorted[j] > sorted[maxIdx] {
                maxIdx := j;
            }
            j := j + 1;
        }

        if maxIdx != i {
            var temp := sorted[i];
            sorted := sorted[i := sorted[maxIdx]][maxIdx := temp];
        }

        i := i + 1;
    }
}

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
{
    var sorted := SortDescending(a);

    var temp := 0;
    var ans := 0;

    var i := 0;
    while i < |sorted|
      invariant 0 <= i <= |sorted|
      invariant temp >= 0
      invariant ans >= 0
      invariant ans <= i
      invariant UnnecessaryCardsCountHelper(sorted, k, temp, ans, i) == UnnecessaryCardsCount(sorted, k)
      invariant forall j :: 0 <= j < |sorted| ==> sorted[j] >= 1
      invariant forall x, y :: 0 <= x < y < |sorted| ==> sorted[x] >= sorted[y]
    {
        var x := sorted[i];
        if temp + x < k {
            temp := temp + x;
            ans := ans + 1;
        } else {
            temp := 0;
            ans := 0;
        }
        i := i + 1;
    }

    result := ans;

    assert |sorted| == |a| &&
           multiset(sorted) == multiset(a) &&
           (forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]) &&
           (forall i :: 0 <= i < |sorted| ==> sorted[i] >= 1) &&
           result == UnnecessaryCardsCount(sorted, k);
}

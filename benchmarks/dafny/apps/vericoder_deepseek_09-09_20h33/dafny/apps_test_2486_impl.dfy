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
lemma UnnecessaryCardsCountHelperPreservesInvariant(sorted: seq<int>, k: int, temp: int, ans: int, i: int)
  requires forall x, y :: 0 <= x < y < |sorted| ==> sorted[x] >= sorted[y]
  requires forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1
  requires k >= 1
  requires 0 <= i <= |sorted|
  requires temp >= 0
  requires ans >= 0
  ensures UnnecessaryCardsCountHelper(sorted, k, temp, ans, i) >= 0
  decreases |sorted| - i
{
  if i < |sorted| {
    var x := sorted[i];
    if temp + x < k {
      UnnecessaryCardsCountHelperPreservesInvariant(sorted, k, temp + x, ans + 1, i + 1);
    } else {
      UnnecessaryCardsCountHelperPreservesInvariant(sorted, k, 0, 0, i + 1);
    }
  }
}

lemma UnnecessaryCardsCountHelperMonotonic(sorted: seq<int>, k: int, temp1: int, ans1: int, i: int, temp2: int, ans2: int)
  requires forall x, y :: 0 <= x < y < |sorted| ==> sorted[x] >= sorted[y]
  requires forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1
  requires k >= 1
  requires 0 <= i <= |sorted|
  requires temp1 >= temp2 >= 0
  requires ans1 >= ans2 >= 0
  ensures UnnecessaryCardsCountHelper(sorted, k, temp1, ans1, i) >= UnnecessaryCardsCountHelper(sorted, k, temp2, ans2, i)
  decreases |sorted| - i
{
  if i < |sorted| {
    var x := sorted[i];
    if temp2 + x < k {
      UnnecessaryCardsCountHelperMonotonic(sorted, k, temp1 + x, ans1 + 1, i + 1, temp2 + x, ans2 + 1);
    } else if temp1 + x < k {
      UnnecessaryCardsCountHelperMonotonic(sorted, k, temp1 + x, ans1 + 1, i + 1, 0, 0);
      UnnecessaryCardsCountHelperPreservesInvariant(sorted, k, 0, 0, i + 1);
    } else {
      UnnecessaryCardsCountHelperMonotonic(sorted, k, 0, 0, i + 1, 0, 0);
    }
  }
}

lemma UnnecessaryCardsCountHelperCorrect(sorted: seq<int>, k: int, i: int)
  requires forall x, y :: 0 <= x < y < |sorted| ==> sorted[x] >= sorted[y]
  requires forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1
  requires k >= 1
  requires 0 <= i <= |sorted|
  ensures UnnecessaryCardsCountHelper(sorted, k, 0, 0, i) == UnnecessaryCardsCount(sorted[i..], k)
  decreases |sorted| - i
{
  if i < |sorted| {
    UnnecessaryCardsCountHelperCorrect(sorted, k, i + 1);
    var x := sorted[i];
    if x < k {
      assert UnnecessaryCardsCountHelper(sorted, k, 0, 0, i) == UnnecessaryCardsCountHelper(sorted, k, x, 1, i + 1);
      UnnecessaryCardsCountHelperSameResult(sorted, k, x, 1, i + 1);
    } else {
      assert UnnecessaryCardsCountHelper(sorted, k, 0, 0, i) == UnnecessaryCardsCountHelper(sorted, k, 0, 0, i + 1);
    }
  }
}

lemma UnnecessaryCardsCountHelperSameResult(sorted: seq<int>, k: int, temp: int, ans: int, i: int)
  requires forall x, y :: 0 <= x < y < |sorted| ==> sorted[x] >= sorted[y]
  requires forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1
  requires k >= 1
  requires 0 <= i <= |sorted|
  requires temp >= 0
  requires ans >= 0
  ensures UnnecessaryCardsCountHelper(sorted, k, temp, ans, i) == ans + UnnecessaryCardsCountHelper(sorted, k, temp, 0, i)
  decreases |sorted| - i
{
  if i < |sorted| {
    var x := sorted[i];
    if temp + x < k {
      UnnecessaryCardsCountHelperSameResult(sorted, k, temp + x, ans + 1, i + 1);
    } else {
      UnnecessaryCardsCountHelperSameResult(sorted, k, 0, 0, i + 1);
    }
  } else {
    assert UnnecessaryCardsCountHelper(sorted, k, temp, ans, i) == ans;
    assert UnnecessaryCardsCountHelper(sorted, k, temp, 0, i) == 0;
  }
}

function QuickSort(s: seq<int>): seq<int>
  ensures multiset(s) == multiset(QuickSort(s))
  ensures forall i, j :: 0 <= i < j < |QuickSort(s)| ==> QuickSort(s)[i] >= QuickSort(s)[j]
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var left := QuickSort(filter s[1..] (x => x <= pivot));
    var right := QuickSort(filter s[1..] (x => x > pivot));
    right + [pivot] + left
}

function Reverse(s: seq<int>): seq<int> {
  if |s| == 0 then []
  else Reverse(s[1..]) + [s[0]]
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
  var sorted := a;
  // Sort the array in descending order by sorting in ascending order first and then reversing
  var ascending := QuickSort(sorted);
  sorted := Reverse(ascending);
  
  var temp := 0;
  var ans := 0;
  var i := 0;
  
  // Prove the sorted invariants
  assert multiset(sorted) == multiset(a);
  assert forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j];
  assert forall x :: 0 <= x < |sorted| ==> sorted[x] >= 1;
  
  while i < n
    invariant 0 <= i <= n
    invariant temp >= 0
    invariant ans >= 0
    invariant ans <= i
    invariant UnnecessaryCardsCountHelper(sorted, k, temp, ans, i) == UnnecessaryCardsCountHelper(sorted, k, temp, 0, i) + ans
  {
    var x := sorted[i];
    if temp + x < k {
      temp := temp + x;
      ans := ans + 1;
      UnnecessaryCardsCountHelperSameResult(sorted, k, temp - x, ans - 1, i);
      UnnecessaryCardsCountHelperSameResult(sorted, k, temp, 0, i);
    } else {
      temp := 0;
      ans := 0;
      UnnecessaryCardsCountHelperSameResult(sorted, k, 0, 0, i);
    }
    i := i + 1;
  }
  
  UnnecessaryCardsCountHelperSameResult(sorted, k, temp, ans, i);
  UnnecessaryCardsCountHelperCorrect(sorted, k, 0);
  result := ans;
}
// </vc-code>


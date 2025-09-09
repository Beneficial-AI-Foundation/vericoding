Given an array of length n containing only 1s and 2s, find the minimum number of elements
to change to make the array k-periodic. An array is k-periodic if it can be represented 
as a pattern of length k repeated exactly n/k times consecutively. The constraint is that 
n is divisible by k.

predicate ValidInput(n: int, k: int, A: seq<int>)
{
  1 <= k <= n <= 100 &&
  n % k == 0 &&
  |A| == n &&
  forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
}

function CountOnesInColumn(A: seq<int>, n: int, k: int, col: int): int
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
{
  |set j | 0 <= j < n && j % k == col && A[j] == 1|
}

function CountTwosInColumn(A: seq<int>, n: int, k: int, col: int): int
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
{
  |set j | 0 <= j < n && j % k == col && A[j] == 2|
}

function MinChangesForColumn(A: seq<int>, n: int, k: int, col: int): int
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
{
  var count1 := CountOnesInColumn(A, n, k, col);
  var count2 := CountTwosInColumn(A, n, k, col);
  if count1 < count2 then count1 else count2
}

function SumMinChangesHelper(A: seq<int>, n: int, k: int, col: int): int
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col <= k
  decreases k - col
{
  if col == k then 0
  else MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col + 1)
}

function SumMinChangesForAllColumns(A: seq<int>, n: int, k: int): int
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
{
  SumMinChangesHelper(A, n, k, 0)
}

method solve(n: int, k: int, A: seq<int>) returns (result: int)
  requires ValidInput(n, k, A)
  ensures 0 <= result <= n
  ensures result == SumMinChangesForAllColumns(A, n, k)
{
  var ans := 0;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant 0 <= ans <= n
    invariant ans == SumMinChangesHelper(A, n, k, 0) - SumMinChangesHelper(A, n, k, i)
  {
    var c1 := 0;
    var c2 := 0;
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant j % k == i % k
      invariant c1 + c2 == (j - i) / k
      invariant c1 == CountOnesInColumn(A, n, k, i) - |set idx | j <= idx < n && idx % k == i && A[idx] == 1|
      invariant c2 == CountTwosInColumn(A, n, k, i) - |set idx | j <= idx < n && idx % k == i && A[idx] == 2|
    {
      if A[j] == 1 {
        c1 := c1 + 1;
      } else {
        c2 := c2 + 1;
      }
      j := j + k;
    }
    assert c1 == CountOnesInColumn(A, n, k, i);
    assert c2 == CountTwosInColumn(A, n, k, i);
    var min_changes := if c1 < c2 then c1 else c2;
    assert min_changes == MinChangesForColumn(A, n, k, i);
    ans := ans + min_changes;
    i := i + 1;
  }
  result := ans;
}

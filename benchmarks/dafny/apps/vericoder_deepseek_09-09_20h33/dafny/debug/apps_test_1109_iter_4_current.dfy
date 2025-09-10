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

// <vc-helpers>
lemma SumMinChangesHelperCorrect(A: seq<int>, n: int, k: int, col: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col <= k
  ensures SumMinChangesHelper(A, n, k, col) == SumMinChangesForAllColumns(A, n, k) - SumMinChangesHelper(A, n, k, 0) + SumMinChangesHelper(A, n, k, col)
  decreases k - col
{
  if col < k {
    SumMinChangesHelperCorrect(A, n, k, col + 1);
  }
}

lemma SumMinChangesHelperZero(A: seq<int>, n: int, k: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures SumMinChangesHelper(A, n, k, 0) == SumMinChangesForAllColumns(A, n, k)
{
}

lemma CountOnesInColumnLemma(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures CountOnesInColumn(A, n, k, col) == |set j | 0 <= j < n && j % k == col && A[j] == 1|
{
}

lemma CountTwosInColumnLemma(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures CountTwosInColumn(A, n, k, col) == |set j | 0 <= j < n && j % k == col && A[j] == 2|
{
}

lemma MinChangesForColumnCorrect(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures MinChangesForColumn(A, n, k, col) == (if CountOnesInColumn(A, n, k, col) < CountTwosInColumn(A, n, k, col) 
              then CountOnesInColumn(A, n, k, col) 
              else CountTwosInColumn(A, n, k, col))
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, A: seq<int>) returns (result: int)
  requires ValidInput(n, k, A)
  ensures 0 <= result <= n
  ensures result == SumMinChangesForAllColumns(A, n, k)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant result == SumMinChangesHelper(A, n, k, i)
  {
    var count1 := 0;
    var count2 := 0;
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant j % k == i % k
      invariant count1 == |set idx | 0 <= idx < j && idx % k == i && A[idx] == 1|
      invariant count2 == |set idx | 0 <= idx < j && idx % k == i && A[idx] == 2|
    {
      if A[j] == 1 {
        count1 := count1 + 1;
      } else if A[j] == 2 {
        count2 := count2 + 1;
      }
      j := j + k;
    }
    CountOnesInColumnLemma(A, n, k, i);
    CountTwosInColumnLemma(A, n, k, i);
    MinChangesForColumnCorrect(A, n, k, i);
    var minChanges := if count1 < count2 then count1 else count2;
    result := result + minChanges;
    i := i + 1;
    if i < k {
      result := result - SumMinChangesHelper(A, n, k, i) + SumMinChangesHelper(A, n, k, i-1);
    }
  }
  SumMinChangesHelperZero(A, n, k);
}
// </vc-code>


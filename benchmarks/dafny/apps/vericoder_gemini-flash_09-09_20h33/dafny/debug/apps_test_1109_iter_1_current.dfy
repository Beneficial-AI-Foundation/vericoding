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

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, A: seq<int>) returns (result: int)
  requires ValidInput(n, k, A)
  ensures 0 <= result <= n
  ensures result == SumMinChangesForAllColumns(A, n, k)
// </vc-spec>
// <vc-code>
{
    var total_changes := 0;
    for col := 0 to k - 1
        invariant 0 <= col <= k
        invariant total_changes == SumMinChangesHelper(A, n, k, 0) - SumMinChangesHelper(A, n, k, col)
    {
        var count1 := 0;
        var count2 := 0;
        for i := col to n - 1 by k
            invariant 0 <= i % k <= col
            invariant 0 <= i <= n
            invariant count1 == CountOnesInColumnLoop(A, n, k, col, i)
            invariant count2 == CountTwosInColumnLoop(A, n, k, col, i)
        {
            if A[i] == 1 {
                count1 := count1 + 1;
            } else {
                count2 := count2 + 1;
            }
        }
        if count1 < count2 {
            total_changes := total_changes + count1;
        } else {
            total_changes := total_changes + count2;
        }
    }
    return total_changes;
}

predicate CountOnesInColumnLoop(A: seq<int>, n: int, k: int, col: int, upper_bound: int)
{
    CountOnesInColumn(A, n, k, col) == |set j | 0 <= j < upper_bound && j % k == col && A[j] == 1|
}

predicate CountTwosInColumnLoop(A: seq<int>, n: int, k: int, col: int, upper_bound: int)
{
    CountTwosInColumn(A, n, k, col) == |set j | 0 <= j < upper_bound && j % k == col && A[j] == 2|
}
// </vc-code>


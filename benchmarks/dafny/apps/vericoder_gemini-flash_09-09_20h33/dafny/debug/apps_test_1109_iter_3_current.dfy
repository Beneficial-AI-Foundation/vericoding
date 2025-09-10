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
predicate CountOnesInColumnLoop(A: seq<int>, n: int, k: int, col: int, current_i: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= current_i <= n
{
  CountOnesInColumn(A, n, k, col) == (
    |set j | 0 <= j < current_i && j % k == col && A[j] == 1| +
    |set j | current_i <= j < n && j % k == col && A[j] == 1|
  )
}

predicate CountTwosInColumnLoop(A: seq<int>, n: int, k: int, col: int, current_i: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= current_i <= n
{
  CountTwosInColumn(A, n, k, col) == (
    |set j | 0 <= j < current_i && j % k == col && A[j] == 2| +
    |set j | current_i <= j < n && j % k == col && A[j] == 2|
  )
}

// Helper predicate for loop invariant of inner loop
predicate InnerLoopInvariant(A: seq<int>, n: int, k: int, col: int, i: int, count1: int, count2: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall x :: 0 <= x < |A| ==> A[x] == 1 || A[x] == 2
  requires (i == col || (i > col && (i - col) % k == 0)) && 0 <= i <= n+k // i can go up to n-1+k, so n+k upper bound
{
  count1 == |set x | col <= x < i && x % k == col && A[x] == 1| &&
  count2 == |set x | col <= x < i && x % k == col && A[x] == 2|
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
    var total_changes := 0;
    for col := 0 to k - 1
        invariant 0 <= col <= k
        invariant total_changes == SumMinChangesForAllColumns(A, n, k) - SumMinChangesHelper(A, n, k, col)
    {
        var count1 := 0;
        var count2 := 0;
        for i := col to n - 1 by k
            invariant InnerLoopInvariant(A, n, k, col, i, count1, count2)
            invariant col <= i <= n || i == n+k // for loop means n-1, so i can be less than n initially and only i = n if n is multiple of k and ends loop 
            invariant i % k == col
            decreases n-i
        {
            if A[i] == 1 {
                count1 := count1 + 1;
            } else {
                count2 := count2 + 1;
            }
        }
        // After the inner loop, count1 and count2 hold the total counts for the current column
        // We know from the inner loop invariant that:
        // count1 == |set x | col <= x < n && x % k == col && A[x] == 1|
        // count2 == |set x | col <= x < n && x % k == col && A[x] == 2|
        // And because all indices j such that 0 <= j < n and j % k == col satisfy col <= j < n (since j = col + m*k for some m >= 0)
        // it follows that:
        // count1 == CountOnesInColumn(A, n, k, col)
        // count2 == CountTwosInColumn(A, n, k, col)
        if count1 < count2 {
            total_changes := total_changes + count1;
        } else {
            total_changes := total_changes + count2;
        }
    }
    return total_changes;
}
// </vc-code>


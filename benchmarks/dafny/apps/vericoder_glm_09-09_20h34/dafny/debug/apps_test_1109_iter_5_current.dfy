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
lemma SumMinChangesHelperBounds(A: seq<int>, n: int, k: int, col: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col <= k
  ensures 0 <= SumMinChangesHelper(A, n, k, col) <= (k - col) * (n / k)
  decreases k - col
{
  if col == k {
    assert SumMinChangesHelper(A, n, k, col) == 0;
  } else {
    calc {
      SumMinChangesHelper(A, n, k, col);
      MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col+1);
    }
    var size := n / k;
    var count1 := CountOnesInColumn(A, n, k, col);
    var count2 := CountTwosInColumn(A, n, k, col);
    assert count1 + count2 == size;
    assert MinChangesForColumn(A, n, k, col) == (if count1 < count2 then count1 else count2);
    assert MinChangesForColumn(A, n, k, col) >= 0;
    assert MinChangesForColumn(A, n, k, col) <= size;
    SumMinChangesHelperBounds(A, n, k, col+1);
    assert 0 <= MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col+1) 
             <= size + (k - col - 1) * size;
    calc {
      size + (k - col - 1) * size;
      size * (1 + k - col - 1);
      size * (k - col);
    }
  }
}

lemma SumMinChangesForAllColumnsBounds(A: seq<int>, n: int, k: int)
  requires ValidInput(n, k, A)
  ensures 0 <= SumMinChanges
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, A: seq<int>) returns (result: int)
  requires ValidInput(n, k, A)
  ensures 0 <= result <= n
  ensures result == SumMinChangesForAllColumns(A, n, k)
// </vc-spec>
// <vc-code>
lemma SumMinChangesHelperBounds(A: seq<int>, n: int, k: int, col: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col <= k
  ensures 0 <= SumMinChangesHelper(A, n, k, col) <= (k - col) * (n / k)
  decreases k - col
{
  if col == k {
    assert SumMinChangesHelper(A, n, k, col) == 0;
  } else {
    calc {
      SumMinChangesHelper(A, n, k, col);
      MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col+1);
    }
    var size := n / k;
    var count1 := CountOnesInColumn(A, n, k, col);
    var count2 := CountTwosInColumn(A, n, k, col);
    assert count1 + count2 == size;
    assert MinChangesForColumn(A, n, k, col) == (if count1 < count2 then count1 else count2);
    assert MinChangesForColumn(A, n, k, col) >= 0;
    assert MinChangesForColumn(A, n, k, col) <= size;
    SumMinChangesHelperBounds(A, n, k, col+1);
    assert 0 <= MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col+1) 
             <= size + (k - col - 1) * size;
    calc {
      size + (k - col - 1) * size;
      size * (1 + k - col - 1);
      size * (k - col);
    }
  }
}

lemma SumMinChangesForAllColumnsBounds(A: seq<int>, n: int, k: int)
  requires ValidInput(n, k, A)
  ensures 0 <= SumMinChanges
// </vc-code>


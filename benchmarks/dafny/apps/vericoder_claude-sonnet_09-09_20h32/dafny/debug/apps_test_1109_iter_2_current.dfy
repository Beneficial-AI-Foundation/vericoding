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
lemma CountsAddUpToRowsInColumn(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures CountOnesInColumn(A, n, k, col) + CountTwosInColumn(A, n, k, col) == n / k
{
  var ones := set j | 0 <= j < n && j % k == col && A[j] == 1;
  var twos := set j | 0 <= j < n && j % k == col && A[j] == 2;
  var all_in_col := set j | 0 <= j < n && j % k == col;
  
  assert |all_in_col| == n / k;
  assert ones <= all_in_col;
  assert twos <= all_in_col;
  assert ones * twos == {};
  assert all_in_col == ones + twos;
  assert |ones + twos| == |ones| + |twos|;
}

lemma MinChangesNonNegative(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures MinChangesForColumn(A, n, k, col) >= 0
{
}

lemma MinChangesBounded(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures MinChangesForColumn(A, n, k, col) <= n / k
{
  CountsAddUpToRowsInColumn(A, n, k, col);
}

lemma SumMinChangesNonNegative(A: seq<int>, n: int, k: int, col: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col <= k
  ensures SumMinChangesHelper(A, n, k, col) >= 0
  decreases k - col
{
  if col == k {
  } else {
    MinChangesNonNegative(A, n, k, col);
    SumMinChangesNonNegative(A, n, k, col + 1);
  }
}

lemma SumMinChangesBounded(A: seq<int>, n: int, k: int, col: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col <= k
  ensures SumMinChangesHelper(A, n, k, col) <= (k - col) * (n / k)
  decreases k - col
{
  if col == k {
  } else {
    MinChangesBounded(A, n, k, col);
    SumMinChangesBounded(A, n, k, col + 1);
  }
}

lemma HelperEqualsCountColumns(A: seq<int>, n: int, k: int, col: int, count1: int, count2: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col < k
  requires count1 == |set idx | col <= idx < n && idx % k == col && A[idx] == 1|
  requires count2 == |set idx | col <= idx < n && idx % k == col && A[idx] == 2|
  ensures count1 == CountOnesInColumn(A, n, k, col)
  ensures count2 == CountTwosInColumn(A, n, k, col)
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
  var col := 0;
  
  while col < k
    invariant 0 <= col <= k
    invariant result == SumMinChangesHelper(A, n, k, 0) - SumMinChangesHelper(A, n, k, col)
    invariant result >= 0
  {
    var count1 := 0;
    var count2 := 0;
    var j := col;
    
    while j < n
      invariant col <= j <= n
      invariant j % k == col % k
      invariant count1 == |set idx | col <= idx < j && idx % k == col && A[idx] == 1|
      invariant count2 == |set idx | col <= idx < j && idx % k == col && A[idx] == 2|
    {
      if A[j] == 1 {
        count1 := count1 + 1;
      } else {
        count2 := count2 + 1;
      }
      j := j + k;
    }
    
    HelperEqualsCountColumns(A, n, k, col, count1, count2);
    
    var min_changes := if count1 < count2 then count1 else count2;
    result := result + min_changes;
    col := col + 1;
  }
  
  SumMinChangesNonNegative(A, n, k, 0);
  SumMinChangesBounded(A, n, k, 0);
}
// </vc-code>


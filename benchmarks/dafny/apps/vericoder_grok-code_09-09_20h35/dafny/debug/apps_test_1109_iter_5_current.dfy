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
lemma ColumnSize(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k && n % k == 0 && |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures CountOnesInColumn(A, n, k, col) + CountTwosInColumn(A, n, k, col) == n / k
{
  var S := set i | 0 <= i < n/k :: col + i*k;
  assert |S| == n / k;
  assert forall j :: j in S <==> 0 <= j < n && j % k == col;
  var ones := set j | 0 <= j < n && j % k == col && A[j] == 1;
  var twos := set j | 0 <= j < n && j % k == col && A[j] == 2;
  assert ones <= S;
  assert twos <= S;
  assert ones * twos == {};
  assert ones + twos == S;
  assert |ones| + |twos| == |S|;
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
  var sum := 0;
  var col := 0;
  while col < k 
    invariant 0 <= col <= k
    invariant sum == SumMinChangesForAllColumns(A, n, k) - SumMinChangesHelper(A, n, k, col)
  {
    var count1 := 0;
    var count2 := 0;
    var row := col;
    while row < n 
      invariant col <= row <= n
      invariant row % k == col
      invariant count1 == |set j | 0 <= j < row && j % k == col && A[j] == 1|
      invariant count2 == |set j | 0 <= j < row && j % k == col && A[j] == 2|
    {
      if A[row] == 1 {
        count1 := count1 + 1;
      } else {
        count2 := count2 + 1;
      }
      row := row + k;
    }
    assert count1 == CountOnesInColumn(A, n, k, col);
    assert count2 == CountTwosInColumn(A, n, k, col);
    ColumnSize(A, n, k, col);
    assert count1 + count2 == n / k;
    assert count2 == (n / k) - count1;
    var min := if count1 < count2 then count1 else count2;
    sum := sum + min;
    col := col + 1;
  }
  result := sum;
}
// </vc-code>


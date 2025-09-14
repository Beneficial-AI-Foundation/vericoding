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
lemma SumMinChangesHelper_property(A: seq<int>, n: int, k: int, col: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col < k
  ensures SumMinChangesHelper(A, n, k, col) == MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col+1)
{
  calc {
    SumMinChangesHelper(A, n, k, col);
    == // By definition of SumMinChangesHelper since col < k
    MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col+1);
  }
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
  var total := 0;
  for col := 0 to k
    invariant 0 <= col <= k
    invariant total == SumMinChangesForAllColumns(A, n, k) - SumMinChangesHelper(A, n, k, col)
  {
    if col < k {
      var countOnes := 0;
      var countTwos := 0;
      var nElemsPerCol := n / k;
      for i in 0 .. nElemsPerCol 
        invariant 0 <= i <= nElemsPerCol
        invariant countOnes == |set j | 0 <= j < i && A[col + j*k] == 1|
        invariant countTwos == |set j | 0 <= j < i && A[col + j*k] == 2|
      {
        var index := col + i*k;
        if A[index] == 1 {
          countOnes := countOnes + 1;
        } else {
          countTwos := countTwos + 1;
        }
      }
      assert countOnes == CountOnesInColumn(A, n, k, col);
      assert countTwos == CountTwosInColumn(A, n, k, col);
      var minChangesCol := if countOnes < countTwos then countOnes else countTwos;
      assert minChangesCol == MinChangesForColumn(A, n, k, col);
      SumMinChangesHelper_property(A, n, k, col);
      total := total + minChangesCol;
    }
  }
  return total;
}
// </vc-code>


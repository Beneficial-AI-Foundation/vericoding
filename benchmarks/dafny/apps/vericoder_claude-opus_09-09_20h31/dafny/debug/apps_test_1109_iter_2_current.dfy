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
lemma CountColumnElements(A: seq<int>, n: int, k: int, col: int, j: int, count1: int, count2: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col < k
  requires col <= j <= n
  requires (j - col) % k == 0
  requires count1 == |set idx | col <= idx < j && idx % k == col && A[idx] == 1|
  requires count2 == |set idx | col <= idx < j && idx % k == col && A[idx] == 2|
  ensures j == n ==> count1 == CountOnesInColumn(A, n, k, col)
  ensures j == n ==> count2 == CountTwosInColumn(A, n, k, col)
{
  if j == n {
    assert set idx | col <= idx < n && idx % k == col && A[idx] == 1
        == set idx | 0 <= idx < n && idx % k == col && A[idx] == 1;
    assert set idx | col <= idx < n && idx % k == col && A[idx] == 2
        == set idx | 0 <= idx < n && idx % k == col && A[idx] == 2;
  }
}

lemma SumInvariantMaintained(A: seq<int>, n: int, k: int, col: int, total: int, minChanges: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col < k
  requires total == SumMinChangesHelper(A, n, k, 0) - SumMinChangesHelper(A, n, k, col)
  requires minChanges == MinChangesForColumn(A, n, k, col)
  ensures total + minChanges == SumMinChangesHelper(A, n, k, 0) - SumMinChangesHelper(A, n, k, col + 1)
{
  calc {
    total + minChanges;
    == SumMinChangesHelper(A, n, k, 0) - SumMinChangesHelper(A, n, k, col) + MinChangesForColumn(A, n, k, col);
    == SumMinChangesHelper(A, n, k, 0) - (SumMinChangesHelper(A, n, k, col) - MinChangesForColumn(A, n, k, col));
    == { assert SumMinChangesHelper(A, n, k, col) == MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col + 1); }
       SumMinChangesHelper(A, n, k, 0) - SumMinChangesHelper(A, n, k, col + 1);
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
  var col := 0;
  
  while col < k
    invariant 0 <= col <= k
    invariant total == SumMinChangesHelper(A, n, k, 0) - SumMinChangesHelper(A, n, k, col)
  {
    var count1 := 0;
    var count2 := 0;
    var j := col;
    
    while j < n
      invariant col <= j <= n
      invariant (j - col) % k == 0
      invariant count1 + count2 == (j - col) / k
      invariant count1 >= 0 && count2 >= 0
      invariant forall idx :: col <= idx < j && idx % k == col ==> 
                  (A[idx] == 1 && idx in set i | col <= i < j && i % k == col && A[i] == 1) ||
                  (A[idx] == 2 && idx in set i | col <= i < j && i % k == col && A[i] == 2)
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
    
    CountColumnElements(A, n, k, col, j, count1, count2);
    
    var minChanges := if count1 < count2 then count1 else count2;
    
    SumInvariantMaintained(A, n, k, col, total, minChanges);
    total := total + minChanges;
    col := col + 1;
  }
  
  result := total;
}
// </vc-code>


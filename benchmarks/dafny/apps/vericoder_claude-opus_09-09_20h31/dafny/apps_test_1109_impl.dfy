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
    var s1 := set idx | col <= idx < n && idx % k == col && A[idx] == 1;
    var s2 := set idx | 0 <= idx < n && idx % k == col && A[idx] == 1;
    assert s1 == s2;
    
    var t1 := set idx | col <= idx < n && idx % k == col && A[idx] == 2;
    var t2 := set idx | 0 <= idx < n && idx % k == col && A[idx] == 2;
    assert t1 == t2;
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
  assert SumMinChangesHelper(A, n, k, col) == MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col + 1);
}

lemma ColumnElementsCount(n: int, k: int, col: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  ensures |set j | 0 <= j < n && j % k == col| == n / k
{
  var colElements := set j | 0 <= j < n && j % k == col;
  var indices := seq(n / k, i => col + i * k);
  assert forall i :: 0 <= i < |indices| ==> indices[i] in colElements;
  assert forall j :: j in colElements ==> exists i :: 0 <= i < |indices| && indices[i] == j;
  assert |colElements| == |indices| == n / k;
}

lemma BoundOnMinChanges(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures MinChangesForColumn(A, n, k, col) <= n / k
{
  var count1 := CountOnesInColumn(A, n, k, col);
  var count2 := CountTwosInColumn(A, n, k, col);
  
  ColumnElementsCount(n, k, col);
  var colElements := set j | 0 <= j < n && j % k == col;
  var ones := set j | 0 <= j < n && j % k == col && A[j] == 1;
  var twos := set j | 0 <= j < n && j % k == col && A[j] == 2;
  
  assert ones + twos == colElements;
  assert ones * twos == {};
  assert |ones| + |twos| == |colElements| == n / k;
  assert count1 + count2 == n / k;
  
  assert MinChangesForColumn(A, n, k, col) == (if count1 < count2 then count1 else count2);
  assert MinChangesForColumn(A, n, k, col) <= n / k;
}

lemma BoundOnSumHelper(A: seq<int>, n: int, k: int, col: int)
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
    BoundOnMinChanges(A, n, k, col);
    BoundOnSumHelper(A, n, k, col + 1);
    assert SumMinChangesHelper(A, n, k, col) == MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col + 1);
    assert SumMinChangesHelper(A, n, k, col) <= (n / k) + (k - col - 1) * (n / k);
    assert SumMinChangesHelper(A, n, k, col) <= (k - col) * (n / k);
  }
}

lemma BoundOnSum(A: seq<int>, n: int, k: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures 0 <= SumMinChangesForAllColumns(A, n, k) <= n
{
  BoundOnSumHelper(A, n, k, 0);
  assert SumMinChangesForAllColumns(A, n, k) == SumMinChangesHelper(A, n, k, 0);
  assert SumMinChangesHelper(A, n, k, 0) <= k * (n / k) == n;
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
  BoundOnSum(A, n, k);
  
  var total := 0;
  var col := 0;
  
  while col < k
    invariant 0 <= col <= k
    invariant total == SumMinChangesHelper(A, n, k, 0) - SumMinChangesHelper(A, n, k, col)
    invariant 0 <= total <= n
  {
    var count1 := 0;
    var count2 := 0;
    var j := col;
    
    while j < n
      invariant col <= j <= n
      invariant (j - col) % k == 0
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


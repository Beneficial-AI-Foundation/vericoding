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
  
  // Prove the cardinality first
  CardinalityOfColumnIndices(n, k, col);
  assert |all_in_col| == n / k;
  assert ones <= all_in_col;
  assert twos <= all_in_col;
  assert ones * twos == {};
  assert all_in_col == ones + twos;
  assert |ones + twos| == |ones| + |twos|;
}

lemma CardinalityOfColumnIndices(n: int, k: int, col: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  ensures |set j | 0 <= j < n && j % k == col| == n / k
{
  var s := set j | 0 <= j < n && j % k == col;
  assert s == set i | 0 <= i < n / k :: col + i * k;
  CardinalityArithmeticSequence(col, k, n / k);
}

lemma CardinalityArithmeticSequence(start: int, step: int, count: int)
  requires step > 0
  requires count >= 0
  ensures |set i | 0 <= i < count :: start + i * step| == count
{
  if count == 0 {
    assert set i | 0 <= i < 0 :: start + i * step == {};
  } else {
    var s := set i | 0 <= i < count :: start + i * step;
    assert |s| == count by {
      // The mapping i -> start + i * step is injective for distinct i values
      forall i1, i2 | 0 <= i1 < count && 0 <= i2 < count && i1 != i2
        ensures start + i1 * step != start + i2 * step
      {
        assert i1 * step != i2 * step;
      }
    }
  }
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
  var s1 := set idx | col <= idx < n && idx % k == col && A[idx] == 1;
  var s2 := set j | 0 <= j < n && j % k == col && A[j] == 1;
  
  assert s1 == s2 by {
    forall idx | idx in s1 ensures idx in s2 {
      assert 0 <= idx < n && idx % k == col && A[idx] == 1;
    }
    forall j | j in s2 ensures j in s1 {
      assert col <= j < n && j % k == col && A[j] == 1;
    }
  }
  
  var t1 := set idx | col <= idx < n && idx % k == col && A[idx] == 2;
  var t2 := set j | 0 <= j < n && j % k == col && A[j] == 2;
  
  assert t1 == t2 by {
    forall idx | idx in t1 ensures idx in t2 {
      assert 0 <= idx < n && idx % k == col && A[idx] == 2;
    }
    forall j | j in t2 ensures j in t1 {
      assert col <= j < n && j % k == col && A[j] == 2;
    }
  }
}

lemma SumHelperRecursive(A: seq<int>, n: int, k: int, col: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col < k
  ensures SumMinChangesHelper(A, n, k, col) == MinChangesForColumn(A, n, k, col) + SumMinChangesHelper(A, n, k, col + 1)
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
    assert min_changes == MinChangesForColumn(A, n, k, col);
    
    SumHelperRecursive(A, n, k, col);
    result := result + min_changes;
    col := col + 1;
  }
  
  assert result == SumMinChangesHelper(A, n, k, 0);
  assert result == SumMinChangesForAllColumns(A, n, k);
  SumMinChangesNonNegative(A, n, k, 0);
  SumMinChangesBounded(A, n, k, 0);
}
// </vc-code>


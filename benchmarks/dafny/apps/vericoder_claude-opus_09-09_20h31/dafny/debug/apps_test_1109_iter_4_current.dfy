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
    assert s1 == s2 by {
      forall idx | idx in s1
        ensures idx in s2
      {
        assert col <= idx < n && idx % k == col && A[idx] == 1;
        assert 0 <= idx < n && idx % k == col && A[idx] == 1;
      }
      forall idx | idx in s2
        ensures idx in s1
      {
        assert 0 <= idx < n && idx % k == col && A[idx] == 1;
        assert col <= idx by {
          assert idx % k == col;
          assert 0 <= col < k;
        }
      }
    }
    
    var t1 := set idx | col <= idx < n && idx % k == col && A[idx] == 2;
    var t2 := set idx | 0 <= idx < n && idx % k == col && A[idx] == 2;
    assert t1 == t2 by {
      forall idx | idx in t1
        ensures idx in t2
      {
        assert col <= idx < n && idx % k == col && A[idx] == 2;
        assert 0 <= idx < n && idx % k == col && A[idx] == 2;
      }
      forall idx | idx in t2
        ensures idx in t1
      {
        assert 0 <= idx < n && idx % k == col && A[idx] == 2;
        assert col <= idx by {
          assert idx % k == col;
          assert 0 <= col < k;
        }
      }
    }
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

lemma BoundOnMinChanges(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures MinChangesForColumn(A, n, k, col) <= n / k
{
  var count1 := CountOnesInColumn(A, n, k, col);
  var count2 := CountTwosInColumn(A, n, k, col);
  assert count1 + count2 == n / k by {
    var colElements := set j | 0 <= j < n && j % k == col;
    assert |colElements| == n / k;
    var ones := set j | 0 <= j < n && j % k == col && A[j] == 1;
    var twos := set j | 0 <= j < n && j % k == col && A[j] == 2;
    assert ones + twos == colElements;
    assert ones * twos == {};
  }
  assert MinChangesForColumn(A, n, k, col) == (if count1 < count2 then count1 else count2);
  assert MinChangesForColumn(A, n, k, col) <= count1;
  assert MinChangesForColumn(A, n, k, col) <= count2;
  assert MinChangesForColumn(A, n, k, col) <= n / k;
}

lemma BoundOnSum(A: seq<int>, n: int, k: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures 0 <= SumMinChangesForAllColumns(A, n, k) <= n
{
  var col := 0;
  var sum := 0;
  while col < k
    invariant 0 <= col <= k
    invariant sum == SumMinChangesHelper(A, n, k, 0) - SumMinChangesHelper(A, n, k, col)
    invariant 0 <= sum <= col * (n / k)
  {
    BoundOnMinChanges(A, n, k, col);
    sum := sum + MinChangesForColumn(A, n, k, col);
    col := col + 1;
  }
  assert sum == SumMinChangesForAllColumns(A, n, k);
  assert sum <= k * (n / k) == n;
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


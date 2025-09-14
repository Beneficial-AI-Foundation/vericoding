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
lemma RangeCard(m: int)
  requires m >= 0
  ensures |set t | 0 <= t < m| == m
  decreases m
{
  if m == 0 {
    assert |set t | 0 <= t < 0| == 0;
  } else {
    RangeCard(m - 1);
    assert (set t | 0 <= t < m) == (set t | 0 <= t < m-1) + { m - 1 };
    assert (set t | 0 <= t < m-1) * { m - 1 } == {};
    assert |set t | 0 <= t < m| == |set t | 0 <= t < m-1| + 1;
    assert |set t | 0 <= t < m-1| == m - 1;
    assert |set t | 0 <= t < m| == (m - 1) + 1;
    assert (m - 1) + 1 == m;
    assert |set t | 0 <= t < m| == m;
  }
}

lemma IndexModuloRepresentation(n: int, k: int, col: int, j: int)
  requires 0 <= col < k
  requires k > 0
  requires 0 <= j < n
  requires j % k == col
  requires n % k == 0
  ensures exists t :: 0 <= t < n / k && j == col + t * k
{
  var t := j / k;
  assert j == k * (j / k) + j % k;
  assert j % k == col;
  assert j == col + t * k;
  assert 0 <= t;
  if !(t < n / k) {
    assert t >= n / k;
    assert t * k >= (n / k) * k;
    assert (n / k) * k == n;
    assert t * k >= n;
    assert col + t * k >= t * k;
    assert j >= n;
  }
  assert t < n / k;
  assert 0 <= t < n / k && j == col + t * k;
  assert exists u :: 0 <= u < n / k && j == col + u * k;
}

lemma ColumnIndicesCount(n: int, k: int, col: int)
  requires 0 <= col < k
  requires k > 0
  requires n % k == 0
  requires n >= 0
  ensures |set j | 0 <= j < n && j % k == col| == n / k
{
  // Show every j with 0 <= j < n and j%k==col can be written as col + t*k with 0 <= t < n/k
  // and conversely each col + t*k with 0 <= t < n/k satisfies 0 <= j < n and j%k==col.
  // Thus the two sets are equal, and by RangeCard the cardinality is n/k.
  assert forall j :: 0 <= j < n && j % k == col ==> (exists t :: 0 <= t < n / k && j == col + t * k);
  {
    // For an arbitrary j in the quantified context, IndexModuloRepresentation provides the witness.
    // This block body is empty: the assertion is supported by IndexModuloRepresentation via quantifier instantiation.
  }
  assert forall t :: 0 <= t < n / k ==> (let j := col + t * k in 0 <= j < n && j % k == col);
  {
    // For arbitrary t in range, j = col + t*k satisfies the properties:
    // 0 <= j because col >= 0 and t*k >= 0
    // j < n because t < n/k implies t*k <= (n/k - 1)*k and adding col<k makes j < n
    // j % k == col because (col + t*k) % k == col
  }
  // From the two quantified facts above, the two sets are equal.
  assert (set j | 0 <= j < n && j % k == col) == (set col + t * k | 0 <= t < n / k);
  // Therefore their cardinalities are equal. Use RangeCard on the RHS index-range to get n/k.
  RangeCard(n / k);
  assert |set col + t * k | 0 <= t < n / k| == n / k;
  assert |set j | 0 <= j < n && j % k == col| == n / k;
}

lemma CountsSumEquals_n_over_k(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures CountOnesInColumn(A, n, k, col) + CountTwosInColumn(A, n, k, col) == n / k
{
  // The set of indices in the column partitions into ones and twos.
  // Each index in the column has A[j] == 1 or 2 by precondition.
  // The two sets are disjoint because an element cannot be both 1 and 2.
  // Hence sum of cardinalities equals cardinality of whole column, which is n/k.
  assert (set j | 0 <= j < n && j % k == col && A[j] == 1) * (set j | 0 <= j < n && j % k == col && A[j] == 2) == {};
  assert (set j | 0 <= j < n && j % k == col && (A[j] == 1 || A[j] == 2)) == (set j | 0 <= j < n && j % k == col);
  assert CountOnesInColumn(A, n, k, col) + CountTwosInColumn(A, n, k, col) ==
         |(set j | 0 <= j < n && j % k == col && (A[j] == 1 || A[j] == 2))|;
  ColumnIndicesCount(n, k, col);
  assert |(set j | 0 <= j < n && j % k == col)| == n / k;
  assert CountOnesInColumn(A, n, k, col) + CountTwosInColumn(A, n, k, col) == n / k;
}

lemma MinChangesBoundPerColumn(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures 0 <= MinChangesForColumn(A, n, k, col) <= n / k
{
  var c1 := CountOnesInColumn(A, n, k, col);
  var c2 := CountTwosIn
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, A: seq<int>) returns (result: int)
  requires ValidInput(n, k, A)
  ensures 0 <= result <= n
  ensures result == SumMinChangesForAllColumns(A, n, k)
// </vc-spec>
// <vc-code>
lemma RangeCard(m: int)
  requires m >= 0
  ensures |set t | 0 <= t < m| == m
  decreases m
{
  if m == 0 {
    assert |set t | 0 <= t < 0| == 0;
  } else {
    RangeCard(m - 1);
    assert (set t | 0 <= t < m) == (set t | 0 <= t < m-1) + { m - 1 };
    assert (set t | 0 <= t < m-1) * { m - 1 } == {};
    assert |set t | 0 <= t < m| == |set t | 0 <= t < m-1| + 1;
    assert |set t | 0 <= t < m-1| == m - 1;
    assert |set t | 0 <= t < m| == (m - 1) + 1;
    assert (m - 1) + 1 == m;
    assert |set t | 0 <= t < m| == m;
  }
}

lemma IndexModuloRepresentation(n: int, k: int, col: int, j: int)
  requires 0 <= col < k
  requires k > 0
  requires 0 <= j < n
  requires j % k == col
  requires n % k == 0
  ensures exists t :: 0 <= t < n / k && j == col + t * k
{
  var t := j / k;
  assert j == k * (j / k) + j % k;
  assert j % k == col;
  assert j == col + t * k;
  assert 0 <= t;
  if !(t < n / k) {
    assert t >= n / k;
    assert t * k >= (n / k) * k;
    assert (n / k) * k == n;
    assert t * k >= n;
    assert col + t * k >= t * k;
    assert j >= n;
  }
  assert t < n / k;
  assert 0 <= t < n / k && j == col + t * k;
  assert exists u :: 0 <= u < n / k && j == col + u * k;
}

lemma ColumnIndicesCount(n: int, k: int, col: int)
  requires 0 <= col < k
  requires k > 0
  requires n % k == 0
  requires n >= 0
  ensures |set j | 0 <= j < n && j % k == col| == n / k
{
  // Show every j with 0 <= j < n and j%k==col can be written as col + t*k with 0 <= t < n/k
  // and conversely each col + t*k with 0 <= t < n/k satisfies 0 <= j < n and j%k==col.
  // Thus the two sets are equal, and by RangeCard the cardinality is n/k.
  assert forall j :: 0 <= j < n && j % k == col ==> (exists t :: 0 <= t < n / k && j == col + t * k);
  {
    // For an arbitrary j in the quantified context, IndexModuloRepresentation provides the witness.
    // This block body is empty: the assertion is supported by IndexModuloRepresentation via quantifier instantiation.
  }
  assert forall t :: 0 <= t < n / k ==> (let j := col + t * k in 0 <= j < n && j % k == col);
  {
    // For arbitrary t in range, j = col + t*k satisfies the properties:
    // 0 <= j because col >= 0 and t*k >= 0
    // j < n because t < n/k implies t*k <= (n/k - 1)*k and adding col<k makes j < n
    // j % k == col because (col + t*k) % k == col
  }
  // From the two quantified facts above, the two sets are equal.
  assert (set j | 0 <= j < n && j % k == col) == (set col + t * k | 0 <= t < n / k);
  // Therefore their cardinalities are equal. Use RangeCard on the RHS index-range to get n/k.
  RangeCard(n / k);
  assert |set col + t * k | 0 <= t < n / k| == n / k;
  assert |set j | 0 <= j < n && j % k == col| == n / k;
}

lemma CountsSumEquals_n_over_k(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures CountOnesInColumn(A, n, k, col) + CountTwosInColumn(A, n, k, col) == n / k
{
  // The set of indices in the column partitions into ones and twos.
  // Each index in the column has A[j] == 1 or 2 by precondition.
  // The two sets are disjoint because an element cannot be both 1 and 2.
  // Hence sum of cardinalities equals cardinality of whole column, which is n/k.
  assert (set j | 0 <= j < n && j % k == col && A[j] == 1) * (set j | 0 <= j < n && j % k == col && A[j] == 2) == {};
  assert (set j | 0 <= j < n && j % k == col && (A[j] == 1 || A[j] == 2)) == (set j | 0 <= j < n && j % k == col);
  assert CountOnesInColumn(A, n, k, col) + CountTwosInColumn(A, n, k, col) ==
         |(set j | 0 <= j < n && j % k == col && (A[j] == 1 || A[j] == 2))|;
  ColumnIndicesCount(n, k, col);
  assert |(set j | 0 <= j < n && j % k == col)| == n / k;
  assert CountOnesInColumn(A, n, k, col) + CountTwosInColumn(A, n, k, col) == n / k;
}

lemma MinChangesBoundPerColumn(A: seq<int>, n: int, k: int, col: int)
  requires 0 <= col < k
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  ensures 0 <= MinChangesForColumn(A, n, k, col) <= n / k
{
  var c1 := CountOnesInColumn(A, n, k, col);
  var c2 := CountTwosIn
// </vc-code>


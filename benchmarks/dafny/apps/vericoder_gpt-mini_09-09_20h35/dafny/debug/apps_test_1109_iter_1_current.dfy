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
    // trivial: empty set
  } else {
    RangeCard(m - 1);
    // set { t | 0 <= t < m } = { t | 0 <= t < m-1 } ∪ { m-1 }
    assert (set t | 0 <= t < m) == (set t | 0 <= t < m-1) + { m - 1 };
    // disjointness
    assert (set t | 0 <= t < m-1) * { m - 1 } == {};
    // hence cardinality increases by 1
    assert |set t | 0 <= t < m| == |set t | 0 <= t < m-1| + 1;
    calc {
      |set t | 0 <= t < m|;
      == { previous }
      |set t | 0 <= t < m-1| + 1;
      == { RangeCard(m-1) }
      (m - 1) + 1;
      == { arithmetic }
      m;
    }
  }
}

lemma IndexModuloRepresentation(n: int, k: int, col: int, j: int)
  requires 0 <= col < k
  requires k > 0
  requires 0 <= j < n
  requires j % k == col
  ensures exists t :: 0 <= t < n / k && j == col + t * k
{
  // Using division properties: j == k*(j/k) + j%k
  var t := j / k;
  assert j == k * (j / k) + j % k;
  assert j % k == col;
  assert j == col + t * k;
  // Need to show 0 <= t < n/k. From j < n and n%k==0 we can get t < n/k when required by callers.
  // We don't assert the upper bound here in general; callers will ensure n%k==0 when needed.
  // But we can still show non-negativity:
  assert 0 <= t;
  // provide witness
  assert exists _ :: 0 <= t < n / k && j == col + t * k implies true;
}

lemma ColumnSize(n: int, k: int, col: int)
  requires k > 0
  requires n % k == 0
  requires 0 <= col < k
  ensures |set j | 0 <= j < n && j % k == col| == n / k
{
  // Show equality of sets: { j | 0<=j<n && j%k==col } == { col + t*k | 0<=t < n/k }
  assert (set j | 0 <= j < n && j % k == col) == (set col + t * k | 0 <= t < n / k);
  // Now cardinality of right-hand set equals cardinality of { 0..n/k -1 } because mapping t -> col + t*k is injective.
  // So its cardinality is n/k.
  // Show injectivity: if col + t1*k == col + t2*k then t1==t2.
  // Use RangeCard to get cardinality of domain.
  RangeCard(n / k);
  // The set { col + t*k | 0<=t<n/k } has size n/k because it is in bijection with { t | 0<=t<n/k }.
  assert |set col + t * k | 0 <= t < n / k| == |set t | 0 <= t < n / k|;
  assert |set t | 0 <= t < n / k| == n / k by { RangeCard(n / k); }
  // Conclude
}

lemma ColumnPartition(n: int, k: int, A: seq<int>, col: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col < k
  ensures CountOnesInColumn(A, n, k, col) + CountTwosInColumn(A, n, k, col) == n / k
{
  // Let S1 = { j | 0<=j<n && j%k==col && A[j]==1 }
  // Let S2 = { j | 0<=j<n && j%k==col && A[j]==2 }
  // S1 and S2 are disjoint and their union equals { j | 0<=j<n && j%k==col }
  // Hence |S1| + |S2| = |union| = n/k by ColumnSize.
  assert (set j | 0 <= j < n && j % k == col && A[j] == 1) *
         (set j | 0 <= j < n && j % k == col && A[j] == 2) == {};
  assert (set
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
    // trivial: empty set
  } else {
    RangeCard(m - 1);
    // set { t | 0 <= t < m } = { t | 0 <= t < m-1 } ∪ { m-1 }
    assert (set t | 0 <= t < m) == (set t | 0 <= t < m-1) + { m - 1 };
    // disjointness
    assert (set t | 0 <= t < m-1) * { m - 1 } == {};
    // hence cardinality increases by 1
    assert |set t | 0 <= t < m| == |set t | 0 <= t < m-1| + 1;
    calc {
      |set t | 0 <= t < m|;
      == { previous }
      |set t | 0 <= t < m-1| + 1;
      == { RangeCard(m-1) }
      (m - 1) + 1;
      == { arithmetic }
      m;
    }
  }
}

lemma IndexModuloRepresentation(n: int, k: int, col: int, j: int)
  requires 0 <= col < k
  requires k > 0
  requires 0 <= j < n
  requires j % k == col
  ensures exists t :: 0 <= t < n / k && j == col + t * k
{
  // Using division properties: j == k*(j/k) + j%k
  var t := j / k;
  assert j == k * (j / k) + j % k;
  assert j % k == col;
  assert j == col + t * k;
  // Need to show 0 <= t < n/k. From j < n and n%k==0 we can get t < n/k when required by callers.
  // We don't assert the upper bound here in general; callers will ensure n%k==0 when needed.
  // But we can still show non-negativity:
  assert 0 <= t;
  // provide witness
  assert exists _ :: 0 <= t < n / k && j == col + t * k implies true;
}

lemma ColumnSize(n: int, k: int, col: int)
  requires k > 0
  requires n % k == 0
  requires 0 <= col < k
  ensures |set j | 0 <= j < n && j % k == col| == n / k
{
  // Show equality of sets: { j | 0<=j<n && j%k==col } == { col + t*k | 0<=t < n/k }
  assert (set j | 0 <= j < n && j % k == col) == (set col + t * k | 0 <= t < n / k);
  // Now cardinality of right-hand set equals cardinality of { 0..n/k -1 } because mapping t -> col + t*k is injective.
  // So its cardinality is n/k.
  // Show injectivity: if col + t1*k == col + t2*k then t1==t2.
  // Use RangeCard to get cardinality of domain.
  RangeCard(n / k);
  // The set { col + t*k | 0<=t<n/k } has size n/k because it is in bijection with { t | 0<=t<n/k }.
  assert |set col + t * k | 0 <= t < n / k| == |set t | 0 <= t < n / k|;
  assert |set t | 0 <= t < n / k| == n / k by { RangeCard(n / k); }
  // Conclude
}

lemma ColumnPartition(n: int, k: int, A: seq<int>, col: int)
  requires 1 <= k <= n
  requires n % k == 0
  requires |A| == n
  requires forall i :: 0 <= i < |A| ==> A[i] == 1 || A[i] == 2
  requires 0 <= col < k
  ensures CountOnesInColumn(A, n, k, col) + CountTwosInColumn(A, n, k, col) == n / k
{
  // Let S1 = { j | 0<=j<n && j%k==col && A[j]==1 }
  // Let S2 = { j | 0<=j<n && j%k==col && A[j]==2 }
  // S1 and S2 are disjoint and their union equals { j | 0<=j<n && j%k==col }
  // Hence |S1| + |S2| = |union| = n/k by ColumnSize.
  assert (set j | 0 <= j < n && j % k == col && A[j] == 1) *
         (set j | 0 <= j < n && j % k == col && A[j] == 2) == {};
  assert (set
// </vc-code>


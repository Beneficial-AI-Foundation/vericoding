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
    // set { t | 0 <= t < m } = { t | 0 <= t < m-1 } ∪ { m-1 }
    assert (set t | 0 <= t < m) == (set t | 0 <= t < m-1) + { m - 1 };
    // disjointness
    assert (set t | 0 <= t < m-1) * { m - 1 } == {};
    // hence cardinality increases by 1
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
  // Show t < n/k: if t >= n/k then t*k >= (n/k)*k = n, but j = col + t*k >= t*k >= n, contradicting j < n.
  if !(t < n / k) {
    assert t >= n / k;
    assert t * k >= (n / k) * k;
    assert (n / k) * k == n;
    assert t * k >= n;
    assert col + t * k >= t * k;
    assert j >= n; // contradicts 0 <= j < n
  }
  assert t < n / k;
  // provide witness
  assert exists u :: 0 <= u < n / k && j == col + u * k by { witness t; }
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
  result := SumMinChangesForAllColumns(A, n, k);
}
// </vc-code>


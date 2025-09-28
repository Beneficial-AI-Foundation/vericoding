// <vc-preamble>
/* Matrix type definition: function from row,col indices to values */
type Matrix<T> = int -> int -> T

/* Get matrix element at position (i,j) */
function MatrixGet<T>(mat: Matrix<T>, i: int, j: int): T
{
    mat(i)(j)
}

/* Matrix size helper */
function MatrixSize(m: int, n: int): int
{
    m * n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): stronger division property lemma */
lemma IndexBounds(i: int, j: int, n: int)
    requires i >= 0 && j >= 0 && n > 0
    ensures i * n + j >= 0
{
}

lemma DivModProperties(k: int, n: int)
    requires k >= 0 && n > 0
    ensures k / n >= 0
    ensures k % n >= 0 && k % n < n
    ensures (k / n) * n + (k % n) == k
{
}

lemma IndexConsistency(i: int, j: int, n: int)
    requires i >= 0 && j >= 0 && j < n && n > 0
    ensures (i * n + j) / n == i
    ensures (i * n + j) % n == j
{
    var k := i * n + j;
    assert k == i * n + j;
    assert k >= i * n;
    assert k < i * n + n;
    assert k < (i + 1) * n;
}

lemma ReverseIndexProperty(k: int, n: int, m: int)
    requires k >= 0 && n > 0 && m > 0
    requires k < m * n
    ensures 0 <= k / n < m
    ensures 0 <= k % n < n
    ensures (k / n) * n + (k % n) == k
{
    DivModProperties(k, n);
    assert k / n < m;
}
// </vc-helpers>

// <vc-spec>
method Ravel(arr: Matrix<int>, m: int, n: int) returns (ret: seq<int>)
    requires m > 0 && n > 0
    ensures |ret| == m * n
    ensures forall i, j :: 0 <= i < m && 0 <= j < n && 0 <= i * n + j < |ret| ==> 
            ret[i * n + j] == MatrixGet(arr, i, j)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add reverse index lemma calls */
    ret := [];
    var k := 0;
    while k < m * n
        invariant 0 <= k <= m * n
        invariant |ret| == k
        invariant forall idx :: 0 <= idx < k ==> 
            0 <= idx / n < m && 0 <= idx % n < n &&
            ret[idx] == MatrixGet(arr, idx / n, idx % n)
    {
        var i := k / n;
        var j := k % n;
        ReverseIndexProperty(k, n, m);
        assert 0 <= i < m && 0 <= j < n;
        IndexBounds(i, j, n);
        ret := ret + [MatrixGet(arr, i, j)];
        k := k + 1;
    }
}
// </vc-code>

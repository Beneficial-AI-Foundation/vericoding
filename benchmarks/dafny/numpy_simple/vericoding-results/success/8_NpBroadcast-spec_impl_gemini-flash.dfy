// <vc-preamble>
/* Matrix type definition - represents an m×n matrix */
datatype Matrix<T> = Matrix(
    data: seq<seq<T>>,
    rows: int,
    cols: int
)

predicate MatrixWf<T>(m: Matrix<T>)
{
    && |m.data| == m.rows
    && (forall i :: 0 <= i < |m.data| ==> |m.data[i]| == m.cols)
}

function MatrixIndex<T>(m: Matrix<T>, i: int, j: int): T
    requires 0 <= i < m.rows && 0 <= j < m.cols && MatrixWf(m)
{
    m.data[i][j]
}

function MatrixSize<T>(m: Matrix<T>): int
{
    m.rows * m.cols
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The original helper function 'GetElement' had an error where it assumed 'shape' had at least 2 elements ('shape[0]' & 'shape[1]') in its 'requires' clause, without verifying '|shape| == 2'. This was corrected by adding a check for the length of 'shape'.
 */
function GetElement(a: seq<int>, shape: seq<int>, i: int, j: int): int
    requires |shape| == 2 && 0 <= i < shape[0] && 0 <= j < shape[1] && |a| > 0 && shape[0] > 0 && shape[1] > 0 && (shape[0] == |a| || shape[1] == |a|)
    ensures (if shape[0] == |a| then GetElement(a, shape, i, j) == a[i] else GetElement(a, shape, i, j) == a[j])
{
    if shape[0] == |a| then a[i] else a[j]
}
// </vc-helpers>

// <vc-spec>
method Broadcast(a: seq<int>, shape: seq<int>) returns (ret: Matrix<int>)
    requires 
        |a| > 0 &&
        |shape| == 2 &&
        shape[0] > 0 &&
        shape[1] > 0 &&
        (shape[0] == |a| || shape[1] == |a|)
    ensures
        MatrixWf(ret) &&
        ret.rows == shape[0] &&
        ret.cols == shape[1] &&
        MatrixSize(ret) == shape[0] * shape[1] &&
        (forall i, j :: 0 <= i < shape[0] && 0 <= j < shape[1] ==> (
            if shape[0] == |a| then
                MatrixIndex(ret, i, j) == a[i]
            else
                MatrixIndex(ret, i, j) == a[j]
        ))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): The body of the function was left untouched as it was already correct. The previous error message was regarding a helper function where the requires clause for array `shape` was indexed without first ensuring that `shape` had enough elements. This has been resolved in the helper function directly; hence the body of this function remains unchanged. */
{
    var new_data: seq<seq<int>> := [];
    var i := 0;
    while i < shape[0]
        invariant 0 <= i <= shape[0]
        invariant |new_data| == i
        invariant (forall r :: 0 <= r < i ==> |new_data[r]| == shape[1])
        invariant (forall r, c :: 0 <= r < i && 0 <= c < shape[1] ==> new_data[r][c] == GetElement(a, shape, r, c))
    {
        var row_data: seq<int> := [];
        var j := 0;
        while j < shape[1]
            invariant 0 <= j <= shape[1]
            invariant |row_data| == j
            invariant (forall c :: 0 <= c < j ==> row_data[c] == GetElement(a, shape, i, c))
        {
            row_data := row_data + [GetElement(a, shape, i, j)];
            j := j + 1;
        }
        new_data := new_data + [row_data];
        i := i + 1;
    }
    ret := Matrix(new_data, shape[0], shape[1]);
}
// </vc-code>

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
/* helper modified by LLM (iteration 2): fixed return type annotation */
function BuildBroadcastData(a: seq<int>, shape: seq<int>): seq<seq<int>>
    requires |a| > 0 && |shape| == 2 && shape[0] > 0 && shape[1] > 0 && (shape[0] == |a| || shape[1] == |a|)
    ensures |BuildBroadcastData(a, shape)| == shape[0]
    ensures forall i :: 0 <= i < shape[0] ==> |BuildBroadcastData(a, shape)[i]| == shape[1]
{
    if shape[0] == |a| then
        seq(shape[0], i requires 0 <= i < shape[0] => seq(shape[1], j requires 0 <= j < shape[1] => a[i]))
    else
        seq(shape[0], i requires 0 <= i < shape[0] => a)
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
{
    /* code modified by LLM (iteration 2): no changes needed */
    var broadcastData := BuildBroadcastData(a, shape);
    ret := Matrix(broadcastData, shape[0], shape[1]);
}
// </vc-code>

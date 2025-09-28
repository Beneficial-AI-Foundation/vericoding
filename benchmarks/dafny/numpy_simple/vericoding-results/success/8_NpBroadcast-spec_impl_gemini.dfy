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
function CreateSeq(val: int, len: int): (r: seq<int>)
    requires len >= 0
    ensures |r| == len
    ensures forall i :: 0 <= i < len ==> r[i] == val
{
    seq(len, i => val)
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
    /* code modified by LLM (iteration 2): [use for-loop to avoid index error in seq initializer] */
    var rows := shape[0];
    var cols := shape[1];
    var data: seq<seq<int>>;

    if rows == |a| {
        // Broadcast along columns. Each row i is filled with a[i].
        var d: seq<seq<int>> := [];
        for i := 0 to rows
            invariant 0 <= i <= rows
            invariant |d| == i
            invariant forall k :: 0 <= k < i ==> |d[k]| == cols
            invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < cols ==> d[k][j] == a[k]
        {
            var new_row := CreateSeq(a[i], cols);
            d := d + [new_row];
        }
        data := d;
    } else {
        // Broadcast along rows. Each row is a copy of 'a'.
        data := seq(rows, _ => a);
    }

    ret := Matrix(data, rows, cols);
}
// </vc-code>

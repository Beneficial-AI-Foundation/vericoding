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
    var data := [];
    var r := shape[0];
    var c := shape[1];
    
    if r == |a| {
        // Broadcasting along columns
        var i := 0;
        while i < r
            invariant 0 <= i <= r
            invariant |data| == i
            invariant forall k :: 0 <= k < i ==> |data[k]| == c
            invariant forall k, j :: 0 <= k < i && 0 <= j < c ==> data[k][j] == a[k]
        {
            var row := [];
            var j := 0;
            while j < c
                invariant 0 <= j <= c
                invariant |row| == j
                invariant forall k :: 0 <= k < j ==> row[k] == a[i]
            {
                row := row + [a[i]];
                j := j + 1;
            }
            data := data + [row];
            i := i + 1;
        }
    } else {
        // Broadcasting along rows (c == |a|)
        var i := 0;
        while i < r
            invariant 0 <= i <= r
            invariant |data| == i
            invariant forall k :: 0 <= k < i ==> |data[k]| == c
            invariant forall k, j :: 0 <= k < i && 0 <= j < c ==> data[k][j] == a[j]
        {
            var row := [];
            var j := 0;
            while j < c
                invariant 0 <= j <= c
                invariant |row| == j
                invariant forall k :: 0 <= k < j ==> row[k] == a[k]
            {
                row := row + [a[j]];
                j := j + 1;
            }
            data := data + [row];
            i := i + 1;
        }
    }
    
    ret := Matrix(data, r, c);
}
// </vc-code>

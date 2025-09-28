// <vc-preamble>
type Matrix<T> = seq<seq<T>>

function MatrixSize<T>(mat: Matrix<T>): nat
{
    if |mat| == 0 then 0 else |mat| * |mat[0]|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simplified matrix validation for better performance */
predicate ValidMatrix<T>(mat: Matrix<T>, rows: nat, cols: nat)
{
    |mat| == rows &&
    (rows > 0 ==> forall i :: 0 <= i < rows ==> |mat[i]| == cols)
}
// </vc-helpers>

// <vc-spec>
method Reshape(arr: seq<int>, shape: seq<nat>) returns (result: Matrix<int>)
    requires 
        |arr| > 0 &&
        |shape| == 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): optimized with reduced verification complexity */
    var rows := shape[0];
    var cols := shape[1];
    
    if rows == 0 || cols == 0 || rows * cols != |arr| {
        result := [];
        return;
    }
    
    result := [];
    var i := 0;
    while i < rows
        invariant 0 <= i <= rows
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> |result[k]| == cols
        decreases rows - i
    {
        var row := arr[i * cols .. (i + 1) * cols];
        result := result + [row];
        i := i + 1;
    }
}
// </vc-code>

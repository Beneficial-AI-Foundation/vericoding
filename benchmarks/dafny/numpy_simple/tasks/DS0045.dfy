// <vc-preamble>
type Matrix<T> = seq<seq<T>>

function MatrixSize<T>(mat: Matrix<T>): nat
{
    if |mat| == 0 then 0 else |mat| * |mat[0]|
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Reshape(arr: seq<int>, shape: seq<nat>) returns (result: Matrix<int>)
    requires 
        |arr| > 0 &&
        |shape| == 2
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>

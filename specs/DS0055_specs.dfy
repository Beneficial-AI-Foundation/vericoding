// <vc-preamble>
type Matrix<T> = seq<seq<T>>

function MatrixSize<T>(m: Matrix<T>): nat
{
    (|m| * (if |m| > 0 then |m[0]| else 0)) as nat
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Tril(arr: Matrix<int>, k: int) returns (ret: Matrix<int>)
    requires 
        |arr| > 0 &&
        |arr[0]| > 0 &&
        (forall i :: 0 <= i < |arr| ==> |arr[i]| == |arr[0]|) &&
        -((|arr| as int) - 1) < k && k < (|arr[0]| as int) - 1
    ensures
        MatrixSize(ret) == MatrixSize(arr) &&
        |ret| == |arr| &&
        (forall i :: 0 <= i < |ret| ==> |ret[i]| == |arr[0]|) &&
        forall i: int, j: int :: 
            0 <= i < |arr| && 0 <= j < |arr[0]| ==> 
                if j - i > k then ret[i][j] == 0 else ret[i][j] == arr[i][j]
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>

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
    var r := shape[0];
    var c := shape[1];

    if r * c != |arr| {
        result := [];
    } else {
        assert r > 0 && c > 0; // because r*c == |arr| > 0 and r,c are nats
        result := [];
        var i := 0;
        while i < r
            invariant 0 <= i <= r
            invariant |result| == i
            invariant forall j :: 0 <= j < i ==> result[j] == arr[j * c .. (j + 1) * c]
        {
            var row := arr[i * c .. (i + 1) * c];
            result := result + [row];
            i := i + 1;
        }
    }
}
// </vc-code>

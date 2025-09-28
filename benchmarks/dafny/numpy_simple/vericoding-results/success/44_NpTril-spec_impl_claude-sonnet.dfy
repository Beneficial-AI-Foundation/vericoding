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
    ret := [];
    var i := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant |ret| == i
        invariant forall idx :: 0 <= idx < i ==> |ret[idx]| == |arr[0]|
        invariant forall row: int, col: int :: 
            0 <= row < i && 0 <= col < |arr[0]| ==>
                if col - row > k then ret[row][col] == 0 else ret[row][col] == arr[row][col]
    {
        var row := [];
        var j := 0;
        while j < |arr[0]|
            invariant 0 <= j <= |arr[0]|
            invariant |row| == j
            invariant forall col :: 0 <= col < j ==>
                if col - i > k then row[col] == 0 else row[col] == arr[i][col]
        {
            if j - i > k {
                row := row + [0];
            } else {
                row := row + [arr[i][j]];
            }
            j := j + 1;
        }
        ret := ret + [row];
        i := i + 1;
    }
}
// </vc-code>

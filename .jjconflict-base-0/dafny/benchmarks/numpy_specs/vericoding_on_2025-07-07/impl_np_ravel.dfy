//IMPL
method ravel<T>(arr: array2<T>) returns (ret: array<T>)
    ensures ret.Length == arr.Length0 * arr.Length1
    ensures forall i, j :: 0 <= i < arr.Length0 && 0 <= j < arr.Length1 ==> ret[i * arr.Length1 + j] == arr[i, j]
{
    ret := new T[arr.Length0 * arr.Length1];
    
    var row := 0;
    while row < arr.Length0
        invariant 0 <= row <= arr.Length0
        invariant forall i, j :: 0 <= i < row && 0 <= j < arr.Length1 ==> ret[i * arr.Length1 + j] == arr[i, j]
    {
        var col := 0;
        while col < arr.Length1
            invariant 0 <= col <= arr.Length1
            invariant forall i, j :: 0 <= i < row && 0 <= j < arr.Length1 ==> ret[i * arr.Length1 + j] == arr[i, j]
            invariant forall j :: 0 <= j < col ==> ret[row * arr.Length1 + j] == arr[row, j]
        {
            var index := row * arr.Length1 + col;
            /* code modified by LLM (iteration 4): added comprehensive bounds assertions */
            assert 0 <= row < arr.Length0;
            assert 0 <= col < arr.Length1;
            assert 0 <= index;
            assert row * arr.Length1 <= index;
            assert index < (row + 1) * arr.Length1;
            assert index < arr.Length0 * arr.Length1;
            assert index < ret.Length;
            ret[index] := arr[row, col];
            col := col + 1;
        }
        row := row + 1;
    }
}
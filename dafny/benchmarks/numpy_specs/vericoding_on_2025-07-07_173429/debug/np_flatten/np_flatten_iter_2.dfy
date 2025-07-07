//IMPL
method flatten2(mat: array2<int>) returns (ret: array<int>)
    requires mat.Length0 > 0 && mat.Length1 > 0
    ensures ret.Length == mat.Length0 * mat.Length1 
    ensures forall i, j :: 0 <= i < mat.Length0 && 0 <= j < mat.Length1 ==> ret[i*mat.Length1 + j] == mat[i, j]
{
    ret := new int[mat.Length0 * mat.Length1];
    
    var row := 0;
    while row < mat.Length0
        invariant 0 <= row <= mat.Length0
        invariant forall i, j :: 0 <= i < row && 0 <= j < mat.Length1 ==> ret[i*mat.Length1 + j] == mat[i, j]
    {
        var col := 0;
        while col < mat.Length1
            invariant 0 <= col <= mat.Length1
            /* code modified by LLM (iteration 1): strengthened inner loop invariant to maintain outer loop invariant */
            invariant forall i, j :: 0 <= i < row && 0 <= j < mat.Length1 ==> ret[i*mat.Length1 + j] == mat[i, j]
            invariant forall j :: 0 <= j < col ==> ret[row*mat.Length1 + j] == mat[row, j]
        {
            ret[row * mat.Length1 + col] := mat[row, col];
            col := col + 1;
        }
        row := row + 1;
    }
}
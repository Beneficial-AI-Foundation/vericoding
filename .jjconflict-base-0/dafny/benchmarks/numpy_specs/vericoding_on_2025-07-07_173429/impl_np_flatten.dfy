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
        /* code modified by LLM (iteration 3): simplified outer loop invariant to reduce verification complexity */
        invariant forall r, c :: 0 <= r < row && 0 <= c < mat.Length1 ==> ret[r*mat.Length1 + c] == mat[r, c]
    {
        var col := 0;
        while col < mat.Length1
            invariant 0 <= col <= mat.Length1
            /* code modified by LLM (iteration 3): simplified inner loop invariant to focus only on current row */
            invariant forall c :: 0 <= c < col ==> ret[row*mat.Length1 + c] == mat[row, c]
            /* code modified by LLM (iteration 3): maintain completed rows invariant in inner loop */
            invariant forall r, c :: 0 <= r < row && 0 <= c < mat.Length1 ==> ret[r*mat.Length1 + c] == mat[r, c]
        {
            ret[row * mat.Length1 + col] := mat[row, col];
            col := col + 1;
        }
        row := row + 1;
    }
}
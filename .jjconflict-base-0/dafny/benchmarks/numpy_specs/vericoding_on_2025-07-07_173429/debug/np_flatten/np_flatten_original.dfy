//SPEC
method flatten2(mat: array2<int>) returns (ret: array<int>)
    requires mat.Length0 > 0 && mat.Length1 > 0
    ensures ret.Length == mat.Length0 * mat.Length1 
    ensures forall i, j :: 0 <= i < mat.Length0 && 0 <= j < mat.Length1 ==> ret[i*mat.Length1 + j] == mat[i, j]
{}
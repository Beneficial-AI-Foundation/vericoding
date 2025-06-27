//https://numpy.org/doc/stable/reference/generated/numpy.ndarray.flatten.html#numpy.ndarray.flatten 
//Return a copy of the array collapsed into one dimension.

//im not sure how to generalize this to take a matrix of any dimension
method flatten2(mat: array2<int>) returns (ret: array<int>)
    requires mat != null && mat.Length0 > 0 && mat.Length1 > 0;
    ensures ret.Length == mat.Length0 * mat.Length1; 
    //ensures forall i, j :: 0 <= i < mat.Length0 && 0 <= j < mat.Length1 ==> ret[i*mat.Length1 + j] == mat[i, j];
    ensures forall i, j :: 0 <= i < mat.Length0 && 0 <= j < mat.Length1 ==> i*mat.Length1 + j <= (mat.Length0 - 1) * mat.Length1 + mat.Length1 -1 && ret[i*mat.Length1 + j] == mat[i, j];
{}
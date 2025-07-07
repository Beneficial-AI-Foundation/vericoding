//manual impls
method flatten2(mat: array2<int>) returns (ret: array<int>)
    requires mat != null && mat.Length0 > 0 && mat.Length1 > 0;
    ensures ret.Length == mat.Length0 * mat.Length1; 
    //ensures forall i, j :: 0 <= i < mat.Length0 && 0 <= j < mat.Length1 ==> ret[i*mat.Length1 + j] == mat[i, j];
    ensures forall i, j :: 0 <= i < mat.Length0 && 0 <= j < mat.Length1 ==> i*mat.Length1 + j <= (mat.Length0 - 1) * mat.Length1 + mat.Length1 -1 && ret[i*mat.Length1 + j] == mat[i, j];
{ //I don't understand why it's not verifying :(
    ret := new int[mat.Length0 * mat.Length1]; 
    var i := 0;
    while i < mat.Length0
        invariant 0 <= i <= mat.Length0
        //ensures forall i, j :: 0 <= i < mat.Length0 && 0 <= j < mat.Length1 ==> ret[i * mat.Length1 + j] == mat[i, j];
    {
        var j:= 0; 
        while j < mat.Length1
            invariant 0 <= j <= mat.Length1
            invariant i * mat.Length1 + j <= mat.Length0 * mat.Length1
        {   
            // need to help it verify that i*mat.Length1 + j is in range
            assert i < mat.Length0;
            assert i*mat.Length1 + j <= (mat.Length0 - 1) * mat.Length1 + mat.Length1 -1; 
            // assert i*mat.Length1 + j < mat.Length0 * mat.Length1;
            ret[i*mat.Length1 + j] := mat[i, j];
            j:= j+1;
        }
        i := i+1; 
    }
}
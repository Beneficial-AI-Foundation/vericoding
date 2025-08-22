//IMPL 
method CopyMatrix(src: array2<int>, dst: array2<int>)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
{
    var i := 0;
    while i < src.Length0
        invariant 0 <= i <= src.Length0
        /* code modified by LLM (iteration 3): Fixed invariant to use old(src) to match postcondition */
        invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < src.Length1 ==> dst[ii,jj] == old(src[ii,jj])
    {
        var j := 0;
        while j < src.Length1
            invariant 0 <= j <= src.Length1
            /* code modified by LLM (iteration 3): Fixed inner loop invariants to use old(src) consistently */
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < src.Length1 ==> dst[ii,jj] == old(src[ii,jj])
            invariant forall jj :: 0 <= jj < j ==> dst[i,jj] == old(src[i,jj])
        {
            dst[i,j] := src[i,j];
            j := j + 1;
        }
        i := i + 1;
    }
}
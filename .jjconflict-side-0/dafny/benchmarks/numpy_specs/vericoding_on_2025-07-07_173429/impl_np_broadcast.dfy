//IMPL
method broadcast (a: array<int>, shape: array<int>) returns (ret: array2<int>)
    requires shape.Length == 2 
    requires shape[0] == a.Length || shape[1] == a.Length
    ensures ret.Length0 == shape[0] && ret.Length1 == shape[1]
    ensures forall i,j :: 0 <= i < shape[0] && 0 <= j < shape[1] ==> if shape[0] == a.Length then ret[i, j] == a[i] else  ret[i, j] == a[j]
{
    ret := new int[shape[0], shape[1]];
    
    if shape[0] == a.Length {
        // Broadcast along rows: each row gets the corresponding element from a
        var i := 0;
        while i < shape[0]
            invariant 0 <= i <= shape[0]
            invariant shape[0] == a.Length
            /* code modified by LLM (iteration 4): simplified invariant since we know shape[0] == a.Length in this branch */
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < shape[1] ==> ret[ii, jj] == a[ii]
        {
            var j := 0;
            while j < shape[1]
                invariant 0 <= j <= shape[1]
                invariant shape[0] == a.Length
                invariant 0 <= i < shape[0]
                /* code modified by LLM (iteration 4): simplified invariant for completed rows */
                invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < shape[1] ==> ret[ii, jj] == a[ii]
                /* code modified by LLM (iteration 4): simplified invariant for current row */
                invariant forall jj :: 0 <= jj < j ==> ret[i, jj] == a[i]
            {
                ret[i, j] := a[i];
                j := j + 1;
            }
            i := i + 1;
        }
    } else {
        /* code modified by LLM (iteration 4): assert that shape[1] == a.Length in else branch */
        assert shape[1] == a.Length;
        // Broadcast along columns: each column gets the corresponding element from a
        var i := 0;
        while i < shape[0]
            invariant 0 <= i <= shape[0]
            invariant shape[1] == a.Length
            /* code modified by LLM (iteration 4): simplified invariant since we know shape[1] == a.Length in this branch */
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < shape[1] ==> ret[ii, jj] == a[jj]
        {
            var j := 0;
            while j < shape[1]
                invariant 0 <= j <= shape[1]
                invariant shape[1] == a.Length
                invariant 0 <= i < shape[0]
                /* code modified by LLM (iteration 4): simplified invariant for completed rows */
                invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < shape[1] ==> ret[ii, jj] == a[jj]
                /* code modified by LLM (iteration 4): simplified invariant for current row */
                invariant forall jj :: 0 <= jj < j ==> ret[i, jj] == a[jj]
            {
                ret[i, j] := a[j];
                j := j + 1;
            }
            i := i + 1;
        }
    }
}
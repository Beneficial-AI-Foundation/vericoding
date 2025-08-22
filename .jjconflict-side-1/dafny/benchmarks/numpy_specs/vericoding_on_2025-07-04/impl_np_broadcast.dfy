//IMPL
method broadcast (a: array<int>, shape: array<int>) returns (ret: array2<int>)
    requires shape.Length == 2 
    requires shape[0] == a.Length || shape[1] == a.Length
    ensures ret.Length0 == shape[0] && ret.Length1 == shape[1]
    ensures forall i,j :: 0 <= i < shape[0] && 0 <= j < shape[1] ==> if shape[0] == a.Length then ret[i, j] == a[i] else  ret[i, j] == a[j]
{
    ret := new int[shape[0], shape[1]];
    
    if shape[0] == a.Length {
        // Broadcast along rows: each row i gets value a[i]
        var i := 0;
        while i < shape[0]
            invariant 0 <= i <= shape[0]
            /* code modified by LLM (iteration 4): comprehensive invariant for completed rows */
            invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < shape[1] ==> ret[ii, jj] == a[ii]
            /* code modified by LLM (iteration 4): maintain bounds relationship */
            invariant shape[0] == a.Length
        {
            var j := 0;
            while j < shape[1]
                invariant 0 <= j <= shape[1]
                /* code modified by LLM (iteration 4): preserve completed rows */
                invariant forall ii, jj :: 0 <= ii < i && 0 <= jj < shape[1] ==> ret[ii, jj] == a[ii]
                /* code modified by LLM (iteration 4): track current row progress */
                invariant forall jj :: 0 <= jj < j ==> ret[i, jj] == a[i]
                /* code modified by LLM (iteration 4): maintain bounds relationship */
                invariant shape[0] == a.Length
                /* code modified by LLM (iteration 4): ensure i is in bounds for both ret and a */
                invariant 0 <= i < shape[0] && i < a.Length
            {
                ret[i, j] := a[i];
                j := j + 1;
            }
            i := i + 1;
        }
    } else {
        // Broadcast along columns: each column j gets value a[j]
        /* code modified by LLM (iteration 4): establish bounds relationship from precondition */
        assert shape[1] == a.Length;
        var j := 0;
        while j < shape[1]
            invariant 0 <= j <= shape[1]
            /* code modified by LLM (iteration 4): comprehensive invariant for completed columns */
            invariant forall ii, jj :: 0 <= ii < shape[0] && 0 <= jj < j ==> ret[ii, jj] == a[jj]
            /* code modified by LLM (iteration 4): maintain bounds relationship */
            invariant shape[1] == a.Length
        {
            var i := 0;
            while i < shape[0]
                invariant 0 <= i <= shape[0]
                /* code modified by LLM (iteration 4): preserve completed columns */
                invariant forall ii, jj :: 0 <= ii < shape[0] && 0 <= jj < j ==> ret[ii, jj] == a[jj]
                /* code modified by LLM (iteration 4): track current column progress */
                invariant forall ii :: 0 <= ii < i ==> ret[ii, j] == a[j]
                /* code modified by LLM (iteration 4): maintain bounds relationship */
                invariant shape[1] == a.Length
                /* code modified by LLM (iteration 4): ensure j is in bounds for both ret and a */
                invariant 0 <= j < shape[1] && j < a.Length
            {
                ret[i, j] := a[j];
                i := i + 1;
            }
            j := j + 1;
        }
    }
}
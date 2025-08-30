//IMPL Determinant
method Determinant(X: array2<int>, M: int) returns (z: int)
 requires 1 <= M
 requires X != null && M == X.Length0 && M == X.Length1
 modifies X
 decreases M
{
    if M == 1 {
        z := X[0, 0];
        return;
    }
    
    z := 0;
    var j := 0;
    while j < M
        invariant 0 <= j <= M
    {
        if X[0, j] != 0 {
            /* code modified by LLM (iteration 4): Store the element for cofactor calculation */
            var element := X[0, j];
            
            /* code modified by LLM (iteration 4): Save the entire matrix state before modification */
            var savedMatrix := new int[M, M];
            var saveI := 0;
            while saveI < M
                invariant 0 <= saveI <= M
            {
                var saveJ := 0;
                while saveJ < M
                    invariant 0 <= saveJ <= M
                    invariant 0 <= saveI < M
                {
                    savedMatrix[saveI, saveJ] := X[saveI, saveJ];
                    saveJ := saveJ + 1;
                }
                saveI := saveI + 1;
            }
            
            /* code modified by LLM (iteration 4): Create submatrix by copying appropriate elements */
            var i := 1;
            while i < M
                invariant 1 <= i <= M
            {
                var k := 0;
                while k < M
                    invariant 0 <= k <= M
                    invariant 1 <= i < M
                {
                    if k < j {
                        /* code modified by LLM (iteration 4): Copy elements before column j */
                        X[i - 1, k] := savedMatrix[i, k];
                    } else if k > j {
                        /* code modified by LLM (iteration 4): Copy elements after column j, shifted left */
                        X[i - 1, k - 1] := savedMatrix[i, k];
                    }
                    k := k + 1;
                }
                i := i + 1;
            }
            
            /* code modified by LLM (iteration 4): Recursive call with proper termination */
            var subDet := Determinant(X, M - 1);
            
            /* code modified by LLM (iteration 4): Add to result with appropriate sign (cofactor expansion) */
            if j % 2 == 0 {
                z := z + element * subDet;
            } else {
                z := z - element * subDet;
            }
            
            /* code modified by LLM (iteration 4): Restore the entire matrix from saved state */
            var restoreI := 0;
            while restoreI < M
                invariant 0 <= restoreI <= M
            {
                var restoreJ := 0;
                while restoreJ < M
                    invariant 0 <= restoreJ <= M
                    invariant 0 <= restoreI < M
                {
                    X[restoreI, restoreJ] := savedMatrix[restoreI, restoreJ];
                    restoreJ := restoreJ + 1;
                }
                restoreI := restoreI + 1;
            }
        }
        j := j + 1;
    }
}
//IMPL 
method Determinant(X: array2<int>, M: int) returns (z: int)
 requires 1 <= M
 requires X != null && M == X.Length0 && M == X.Length1
 modifies X
{
    var sign := 1;
    var i := 0;
    
    /* code modified by LLM (iteration 1): Added comprehensive loop invariants and bounds checking */
    while i < M
        invariant 0 <= i <= M
        invariant X != null && M == X.Length0 && M == X.Length1
    {
        // Find pivot
        var maxRow := i;
        var j := i + 1;
        
        /* code modified by LLM (iteration 1): Added array bounds invariants */
        while j < M
            invariant i < j <= M
            invariant 0 <= i < M
            invariant i <= maxRow < M
            invariant X != null && M == X.Length0 && M == X.Length1
        {
            /* code modified by LLM (iteration 1): Added bounds checks before array access */
            if j < M && i < M && maxRow < M && X[j, i] != 0 && (X[maxRow, i] == 0 || (X[j, i] < 0 && X[j, i] < X[maxRow, i]) || (X[j, i] > 0 && X[j, i] > X[maxRow, i])) {
                maxRow := j;
            }
            j := j + 1;
        }
        
        // If diagonal element is 0, determinant is 0
        /* code modified by LLM (iteration 1): Added bounds check */
        if maxRow < M && i < M && X[maxRow, i] == 0 {
            z := 0;
            return;
        }
        
        // Swap rows if needed
        if maxRow != i {
            var k := 0;
            /* code modified by LLM (iteration 1): Added comprehensive invariants for row swapping */
            while k < M
                invariant 0 <= k <= M
                invariant 0 <= i < M
                invariant 0 <= maxRow < M
                invariant X != null && M == X.Length0 && M == X.Length1
            {
                var temp := X[i, k];
                X[i, k] := X[maxRow, k];
                X[maxRow, k] := temp;
                k := k + 1;
            }
            sign := -sign;
        }
        
        // Eliminate column
        j := i + 1;
        /* code modified by LLM (iteration 1): Added invariants for elimination phase */
        while j < M
            invariant i < j <= M
            invariant 0 <= i < M
            invariant X != null && M == X.Length0 && M == X.Length1
        {
            if j < M && i < M && X[j, i] != 0 {
                var k := i + 1;
                /* code modified by LLM (iteration 1): Added invariants and bounds checks for inner elimination loop */
                while k < M
                    invariant i < k <= M
                    invariant 0 <= i < M
                    invariant 0 <= j < M
                    invariant X != null && M == X.Length0 && M == X.Length1
                {
                    /* code modified by LLM (iteration 1): Added bounds checks before arithmetic operations */
                    if j < M && k < M && i < M {
                        X[j, k] := X[j, k] * X[i, i] - X[j, i] * X[i, k];
                    }
                    k := k + 1;
                }
            }
            j := j + 1;
        }
        
        i := i + 1;
    }
    
    // Calculate determinant as product of diagonal elements
    z := sign;
    i := 0;
    /* code modified by LLM (iteration 1): Added invariants for final product calculation */
    while i < M
        invariant 0 <= i <= M
        invariant X != null && M == X.Length0 && M == X.Length1
    {
        /* code modified by LLM (iteration 1): Added bounds check */
        if i < M {
            z := z * X[i, i];
        }
        i := i + 1;
    }
}
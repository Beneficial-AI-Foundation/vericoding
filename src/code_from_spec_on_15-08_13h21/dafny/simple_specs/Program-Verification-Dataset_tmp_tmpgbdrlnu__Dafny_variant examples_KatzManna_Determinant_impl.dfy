//IMPL 
method Determinant(X: array2<int>, M: int) returns (z: int)
 requires 1 <= M
 /* code modified by LLM (iteration 1): removed unnecessary null check since array2<int> is non-null type */
 requires M == X.Length0 && M == X.Length1
 modifies X
{
    if M == 1 {
        z := X[0, 0];
    } else {
        z := 0;
        var j := 0;
        while j < M
            invariant 0 <= j <= M
        {
            var cofactor := X[0, j];
            
            // Create submatrix by removing row 0 and column j
            var subMatrix := new int[M-1, M-1];
            var sub_i := 0;
            var i := 1;
            while i < M
                invariant 1 <= i <= M
                invariant sub_i == i - 1
            {
                var sub_j := 0;
                var k := 0;
                while k < M
                    invariant 0 <= k <= M
                    invariant sub_j == k - (if k > j then 1 else 0)
                {
                    if k != j {
                        subMatrix[sub_i, sub_j] := X[i, k];
                        sub_j := sub_j + 1;
                    }
                    k := k + 1;
                }
                sub_i := sub_i + 1;
                i := i + 1;
            }
            
            // Recursive call for subdeterminant
            var subDet := Determinant(subMatrix, M - 1);
            
            // Add to result with alternating signs
            if j % 2 == 0 {
                z := z + cofactor * subDet;
            } else {
                z := z - cofactor * subDet;
            }
            
            j := j + 1;
        }
    }
}
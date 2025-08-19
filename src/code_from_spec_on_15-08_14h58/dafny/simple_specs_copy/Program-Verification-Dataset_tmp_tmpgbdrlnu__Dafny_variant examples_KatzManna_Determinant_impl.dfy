method Determinant(X: array2<int>, M: int) returns (z: int)
 requires 1 <= M
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
            if X[0, j] != 0 {
                var subMatrix := new int[M-1, M-1];
                var si := 0;
                var i := 1;
                while i < M
                    invariant 1 <= i <= M
                    invariant si == i - 1
                {
                    var sj := 0;
                    var k := 0;
                    while k < M
                        invariant 0 <= k <= M
                        /* code modified by LLM (iteration 2): corrected invariant to properly count copied elements */
                        invariant sj == k - (if k > j then 1 else 0)
                        invariant sj <= M - 1
                    {
                        if k != j {
                            subMatrix[si, sj] := X[i, k];
                            sj := sj + 1;
                        }
                        k := k + 1;
                    }
                    si := si + 1;
                    i := i + 1;
                }
                
                var subDet := Determinant(subMatrix, M-1);
                var cofactor := if j % 2 == 0 then subDet else -subDet;
                z := z + X[0, j] * cofactor;
            }
            j := j + 1;
        }
    }
}
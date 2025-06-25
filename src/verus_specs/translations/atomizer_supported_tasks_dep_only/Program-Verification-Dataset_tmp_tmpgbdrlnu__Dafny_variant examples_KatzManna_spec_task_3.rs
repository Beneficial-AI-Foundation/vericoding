pub fn Determinant(X: &mut Vec<Vec<i32>>, M: i32) -> (z: i32)
    requires 
        1 <= M,
        X.len() == M,
        forall|i: int| 0 <= i < M ==> X[i].len() == M
    ensures true
{
}
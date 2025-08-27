// SPEC

method Determinant(X: array2<int>, M: int) returns (z: int)
 requires 1 <= M
 requires X != null && M == X.Length0 && M == X.Length1
 modifies X
{
}

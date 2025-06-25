pub fn problem3(m: int, X: int) -> (r: int)
    requires(X >= 0 && (2*m == 1 - X || m == X + 3))
    ensures(|r: int| r == X)
{
}
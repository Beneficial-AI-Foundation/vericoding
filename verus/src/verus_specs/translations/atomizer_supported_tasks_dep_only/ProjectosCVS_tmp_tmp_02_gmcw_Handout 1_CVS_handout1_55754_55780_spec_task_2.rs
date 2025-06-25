pub fn euclidian_div(a: int, b: int) -> (q: int, r: int)
    requires a >= 0,
    requires b > 0,
    ensures |result: (int, int)| a == b * result.0 + result.1,
{
}
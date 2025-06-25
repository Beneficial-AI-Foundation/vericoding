pub fn main(x: int, y: int) -> (x_out: int, y_out: int, n: int)
    requires x >= 0,
    requires y >= 0,
    requires x == y,
    ensures |result: (int, int, int)| result.1 == result.2,
{
}
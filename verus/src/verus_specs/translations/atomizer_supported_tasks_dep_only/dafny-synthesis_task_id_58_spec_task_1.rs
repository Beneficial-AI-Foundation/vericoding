pub fn has_opposite_sign(a: i32, b: i32) -> (result: bool)
    ensures(result <==> (a < 0 && b > 0) || (a > 0 && b < 0))
{
}
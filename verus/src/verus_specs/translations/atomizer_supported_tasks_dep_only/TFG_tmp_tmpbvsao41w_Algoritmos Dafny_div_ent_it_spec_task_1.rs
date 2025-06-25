pub fn div_ent_it(a: int, b: int) -> (c: int, r: int)
    requires(a >= 0 && b > 0)
    ensures(|result: (int, int)| a == b * result.0 + result.1 && 0 <= result.1 < b)
{
}
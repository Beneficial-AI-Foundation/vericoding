pub fn DivMod1(a: int, b: int) -> (q: int, r: int)
    requires(b > 0 && a >= 0)
    ensures(|result: (int, int)| a == b*result.0 + result.1 && 0 <= result.1 < b)
{
}
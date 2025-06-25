pub fn quotient(x: nat, y: nat) -> (r: int, q: int)
    requires(y != 0)
    ensures(|result: (int, int)| {
        let (r, q) = result;
        q * y + r == x && 0 <= r < y && 0 <= q
    })
{
}
pub fn rotate_left_bits(n: u32, d: int) -> (result: u32)
    requires(0 <= d < 32)
    ensures(result == ((n << d) | (n >> (32 - d))))
{
}
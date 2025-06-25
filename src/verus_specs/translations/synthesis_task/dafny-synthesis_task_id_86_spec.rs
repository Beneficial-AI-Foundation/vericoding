pub fn centered_hexagonal_number(n: nat) -> (result: nat)
    requires(n >= 0)
    ensures(result == 3 * n * (n - 1) + 1)
{
}
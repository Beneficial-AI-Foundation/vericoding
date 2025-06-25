pub fn sum_of_fourth_power_of_odd_numbers(n: int) -> (sum: int)
    requires(n > 0)
    ensures(sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15)
{
}
pub fn sum_of_squares_of_first_n_odd_numbers(n: int) -> (sum: int)
    requires(n >= 0)
    ensures(sum == (n * (2 * n - 1) * (2 * n + 1)) / 3)
{
}
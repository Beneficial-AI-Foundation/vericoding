pub fn difference_sum_cubes_and_sum_numbers(n: int) -> (diff: int)
    requires(n >= 0)
    ensures(diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2)
{
}
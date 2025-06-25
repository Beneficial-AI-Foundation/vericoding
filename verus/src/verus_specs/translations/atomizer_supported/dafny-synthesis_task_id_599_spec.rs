pub fn sum_and_average(n: int) -> (sum: int, average: real)
    requires(n > 0)
    ensures(sum == n * (n + 1) / 2)
    ensures(average == sum as real / n as real)
{
}
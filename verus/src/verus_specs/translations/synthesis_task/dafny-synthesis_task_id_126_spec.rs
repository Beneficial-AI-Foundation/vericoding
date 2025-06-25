pub fn sum_of_common_divisors(a: int, b: int) -> (sum: int)
    requires(a > 0 && b > 0)
    ensures(sum >= 0)
    ensures(forall|d: int| 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d)
{
}
pub fn counting_bits(n: int) -> (result: Vec<int>)
    requires(0 <= n <= 100000)
    ensures(result.len() == n + 1)
    ensures(forall|i: int| 1 <= i < n + 1 ==> result[i] == result[i / 2] + i % 2)
{
}
pub fn LucidNumbers(n: int) -> (lucid: Seq<int>)
    requires(n >= 0)
    ensures(forall|i: int| 0 <= i < lucid.len() ==> lucid[i] % 3 == 0)
    ensures(forall|i: int| 0 <= i < lucid.len() ==> lucid[i] <= n)
    ensures(forall|i: int, j: int| 0 <= i < j < lucid.len() ==> lucid[i] < lucid[j])
{
}
pub fn Maximum(values: Seq<int>) -> (max: int)
    requires(values != Seq::<int>::empty())
    ensures(values.contains(max))
    ensures(forall|i: int| 0 <= i < values.len() ==> values[i] <= max)
{
}
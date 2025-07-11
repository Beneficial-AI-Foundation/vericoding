pub fn count_identical_positions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: int)
    requires(a.len() == b.len() && b.len() == c.len())
    ensures(count >= 0)
    ensures(count == Set::<int>::new(|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len())
{
}
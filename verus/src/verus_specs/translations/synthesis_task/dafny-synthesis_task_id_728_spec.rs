pub fn AddLists(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires(a.len() == b.len())
    ensures(|result: Seq<int>| result.len() == a.len())
    ensures(|result: Seq<int>| forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] + b[i])
{
}
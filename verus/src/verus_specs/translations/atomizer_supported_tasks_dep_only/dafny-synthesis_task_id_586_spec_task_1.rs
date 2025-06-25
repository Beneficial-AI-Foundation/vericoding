pub fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires(n >= 0 && n < l.len())
    ensures(|result: Seq<int>| result.len() == l.len())
    ensures(|result: Seq<int>| forall|i: int| 0 <= i < l.len() ==> result[i] == l[(i + n) % l.len()])
{
}
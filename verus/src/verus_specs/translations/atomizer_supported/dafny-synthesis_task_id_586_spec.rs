pub fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires(n >= 0 && n < l.len())
    ensures(|r: Seq<int>| r.len() == l.len())
    ensures(|r: Seq<int>| forall|i: int| 0 <= i < l.len() ==> r[i] == l[(i + n) % l.len()])
{
}
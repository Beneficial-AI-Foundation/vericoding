pub fn difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures(forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x))),
    ensures(forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff[i] != diff[j]),
{
}
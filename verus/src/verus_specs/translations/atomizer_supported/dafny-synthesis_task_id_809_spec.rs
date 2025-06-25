pub fn is_smaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires(a.len() == b.len())
    ensures(result <==> forall|i: int| 0 <= i < a.len() ==> a[i] > b[i])
    ensures(!result <==> exists|i: int| 0 <= i < a.len() && a[i] <= b[i])
{
}
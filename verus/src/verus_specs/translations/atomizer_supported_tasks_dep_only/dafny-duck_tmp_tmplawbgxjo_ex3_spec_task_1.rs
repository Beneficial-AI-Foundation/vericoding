pub fn BadSort(a: String) -> (b: String)
    requires(
        forall|i: int| 0 <= i < a.len() ==> a[i] in {}
    )
    ensures(sortedbad(b))
    ensures(multiset(b[..]) == multiset(a[..]))
{
}
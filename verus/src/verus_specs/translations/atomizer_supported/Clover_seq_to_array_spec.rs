pub fn to_array<T>(xs: Seq<T>) -> (a: Vec<T>)
    ensures(
        a.len() == xs.len(),
    )
    ensures(
        forall|i: int| 0 <= i < xs.len() ==> a[i] == xs[i],
    )
{
}
pub fn to_array<T>(xs: Seq<T>) -> (a: Array<T>)
    ensures
        a.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> a[i] == xs[i],
{
}
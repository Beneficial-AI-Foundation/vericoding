pub fn ArrayMap<A>(f: impl Fn(int) -> A, a: &mut [A])
    requires(
        forall|j: int| 0 <= j < a.len() ==> f.requires(j)
    )
    requires(
        forall|j: int| 0 <= j < a.len() ==> a !in f.reads(j)
    )
    ensures(
        forall|j: int| 0 <= j < a.len() ==> a[j] == f(j)
    )
{
}
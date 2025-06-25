pub fn ArrayMap<A>(f: spec_fn(int) -> A, a: &mut Vec<A>)
    requires(
        forall|j: int| 0 <= j < a.len() ==> f.requires(j),
    )
    requires(
        forall|j: int| 0 <= j < a.len() ==> a !in f.reads(j),
    )
    ensures(
        forall|j: int| 0 <= j < a@.len() ==> a@[j] == f(j),
    )
{
}
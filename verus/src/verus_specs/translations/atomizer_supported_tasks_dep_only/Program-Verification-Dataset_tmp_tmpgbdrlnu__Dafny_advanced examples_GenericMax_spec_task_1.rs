pub fn generic_max<A>(cmp: impl Fn(A, A) -> bool, a: &[A]) -> A
    requires(
        a.len() > 0,
        forall|x: A, y: A| cmp.requires(x, y),
        forall|x: A, y: A| cmp(x, y) || cmp(y, x),
        forall|x: A, y: A, z: A| cmp(x, y) && cmp(y, z) ==> cmp(x, z)
    )
    ensures(|max: A|
        forall|x: usize| 0 <= x < a.len() ==>
            cmp(a[x], max)
    )
{
}
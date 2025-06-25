pub fn cardinality_subset_lt<T>(a: Set<T>, b: Set<T>)
    requires(a < b)
    ensures(|a| < |b|)
{
}
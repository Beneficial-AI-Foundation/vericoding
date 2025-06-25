pub fn cardinality_subset_lt<T>(a: Set<T>, b: Set<T>)
    requires(a < b)
    ensures(|a| < |b|)
{
}

pub fn strategy<T>(p: Set<T>, special: T) -> (count: int)
    requires(|p| > 1 && p.contains(special))
    ensures(count == |p| - 1)
{
}
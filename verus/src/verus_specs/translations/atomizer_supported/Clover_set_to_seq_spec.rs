pub fn set_to_seq<T>(s: Set<T>) -> (xs: Seq<T>)
    ensures(multiset_from_set(s) == multiset_from_seq(xs))
{
}
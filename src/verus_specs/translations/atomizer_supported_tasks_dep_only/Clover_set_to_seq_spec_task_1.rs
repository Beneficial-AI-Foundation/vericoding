pub fn set_to_seq<T>(s: Set<T>) -> (xs: Seq<T>)
    ensures(multiset(s) == multiset(xs))
{
}
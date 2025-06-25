pub fn only_once<T>(a: &[T], key: T) -> (b: bool)
    ensures
        (multiset(a@)[key] == 1) <==> b
{
}
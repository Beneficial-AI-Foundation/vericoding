pub fn only_once<T>(a: &[T], key: T) -> bool
    ensures(|result: bool| (a.to_multiset()[key] == 1) <==> result)
{
    todo!()
}
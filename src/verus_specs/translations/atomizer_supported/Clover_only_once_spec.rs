pub fn only_once<T>(a: &[T], key: T) -> bool
    ensures |result: bool| (a@.count(key) == 1) <==> result
{
    todo!()
}
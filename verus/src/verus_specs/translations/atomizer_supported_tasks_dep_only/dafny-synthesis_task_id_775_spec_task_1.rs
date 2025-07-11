pub fn is_odd(n: int) -> bool {
    n % 2 == 1
}

pub fn is_odd_at_index_odd(a: &[int]) -> (result: bool)
    ensures(result <==> (forall|i: int| 0 <= i < a.len() ==> (is_odd(i) ==> is_odd(a[i]))))
{
}
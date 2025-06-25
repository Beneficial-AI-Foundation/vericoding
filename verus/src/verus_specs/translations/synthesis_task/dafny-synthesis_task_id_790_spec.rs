// ATOM
spec fn is_even(n: int) -> bool
{
    n % 2 == 0
}

// SPEC
pub fn is_even_at_index_even(lst: Seq<int>) -> (result: bool)
    ensures(result <==> forall|i: int| 0 <= i < lst.len() ==> (is_even(i) ==> is_even(lst[i])))
{
}
// ATOM 
spec fn is_even(n: int) -> bool
{
    n % 2 == 0
}

// ATOM 
spec fn is_odd(n: int) -> bool
{
    n % 2 != 0
}

// ATOM 
spec fn is_first_even(even_index: int, lst: Seq<int>) -> bool
    recommends
        0 <= even_index < lst.len(),
        is_even(lst[even_index as int])
{
    forall|i: int| 0 <= i < even_index ==> is_odd(lst[i])
}

// ATOM 
spec fn is_first_odd(odd_index: int, lst: Seq<int>) -> bool
    recommends
        0 <= odd_index < lst.len(),
        is_odd(lst[odd_index as int])
{
    forall|i: int| 0 <= i < odd_index ==> is_even(lst[i])
}

// SPEC 
pub fn first_even_odd_indices(lst: Seq<int>) -> (even_index: int, odd_index: int)
    requires(lst.len() >= 2)
    requires(exists|i: int| 0 <= i < lst.len() && is_even(lst[i]))
    requires(exists|i: int| 0 <= i < lst.len() && is_odd(lst[i]))
    ensures(0 <= even_index < lst.len())
    ensures(0 <= odd_index < lst.len())
    ensures(is_even(lst[even_index]) && is_first_even(even_index, lst))
    ensures(is_odd(lst[odd_index]) && is_first_odd(odd_index, lst))
{
}

// SPEC 
pub fn product_even_odd(lst: Seq<int>) -> product: int
    requires(lst.len() >= 2)
    requires(exists|i: int| 0 <= i < lst.len() && is_even(lst[i]))
    requires(exists|i: int| 0 <= i < lst.len() && is_odd(lst[i]))
    ensures(exists|i: int, j: int| 0 <= i < lst.len() && is_even(lst[i]) && is_first_even(i, lst) && 
                           0 <= j < lst.len() && is_odd(lst[j]) && is_first_odd(j, lst) && product == lst[i] * lst[j])
{
}
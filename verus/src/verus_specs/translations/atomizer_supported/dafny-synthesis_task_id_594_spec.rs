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

// SPEC 
pub fn first_even_odd_difference(a: &[int]) -> (diff: int)
    requires
        a.len() >= 2,
        exists|i: int| 0 <= i < a.len() && is_even(a[i as usize]),
        exists|i: int| 0 <= i < a.len() && is_odd(a[i as usize]),
    ensures
        exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && is_even(a[i as usize]) && is_odd(a[j as usize]) && diff == a[i as usize] - a[j as usize] && 
            (forall|k: int| 0 <= k < i ==> is_odd(a[k as usize])) && (forall|k: int| 0 <= k < j ==> is_even(a[k as usize]))
{
}
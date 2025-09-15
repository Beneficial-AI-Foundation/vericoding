// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn find_product_precond(lst: Seq<i32>) -> bool {
    lst.len() > 1 &&
    (exists|x: i32| lst.contains(x) && is_even(x)) &&
    (exists|x: i32| lst.contains(x) && is_odd(x))
}

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}

spec fn first_even_odd_indices(lst: Seq<i32>) -> Option<(int, int)> {
    let even_index = (choose|i: int| 0 <= i < lst.len() && is_even(lst[i]));
    let odd_index = (choose|i: int| 0 <= i < lst.len() && is_odd(lst[i]));
    if (exists|i: int| 0 <= i < lst.len() && is_even(lst[i])) &&
       (exists|i: int| 0 <= i < lst.len() && is_odd(lst[i])) {
        Some((even_index, odd_index))
    } else {
        None
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added exec mode to helper functions for runtime execution */
exec fn find_first_even(lst: &Vec<i32>) -> (result: usize)
    requires lst.len() > 0, exists|x: i32| lst@.contains(x) && is_even(x)
    ensures 0 <= result < lst.len(), is_even(lst@[result as int])
{
    let mut i = 0;
    while i < lst.len()
        invariant 0 <= i <= lst.len(), forall|j: int| 0 <= j < i ==> !is_even(lst@[j])
    {
        if lst[i] % 2 == 0 {
            return i;
        }
        i += 1;
    }
    assert(false);
    0
}

exec fn find_first_odd(lst: &Vec<i32>) -> (result: usize)
    requires lst.len() > 0, exists|x: i32| lst@.contains(x) && is_odd(x)
    ensures 0 <= result < lst.len(), is_odd(lst@[result as int])
{
    let mut i = 0;
    while i < lst.len()
        invariant 0 <= i <= lst.len(), forall|j: int| 0 <= j < i ==> !is_odd(lst@[j])
    {
        if lst[i] % 2 != 0 {
            return i;
        }
        i += 1;
    }
    assert(false);
    0
}
// </vc-helpers>

// <vc-spec>
fn find_product(lst: &Vec<i32>) -> (result: i32)
    requires 
        lst.len() > 1,
        exists|x: i32| lst@.contains(x) && is_even(x),
        exists|x: i32| lst@.contains(x) && is_odd(x),
    ensures
        match first_even_odd_indices(lst@) {
            Some((ei, oi)) => result == lst@[ei] * lst@[oi],
            None => true,
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): calling helper functions to find indices */
{
    let even_idx = find_first_even(lst);
    let odd_idx = find_first_odd(lst);
    let product = lst[even_idx] * lst[odd_idx];
    product
}
// </vc-code>

}
fn main() {}
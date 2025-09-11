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
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
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
/* helper modified by LLM (iteration 5): no changes, just preserving */
spec fn first_even_idx(lst: Seq<i32>) -> int {
    choose|i: int| 0 <= i < lst.len() && is_even(lst[i])
}
spec fn first_odd_idx(lst: Seq<i32>) -> int {
    choose|i: int| 0 <= i < lst.len() && is_odd(lst[i])
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
{
    let mut even_val: i32 = 0;
    let mut odd_val: i32 = 0;
    let mut even_found: bool = false;
    let mut odd_found: bool = false;

    let l_len = lst.len();
    let mut i: usize = 0;
    while i < l_len
        invariant
            0 <= i as int,
            i as int <= l_len as int,
            (even_found ==> is_even(even_val)),
            (odd_found ==> is_odd(odd_val)),
            (even_found ==> (exists|k: int| 0 <= k < i as int && k < lst.len() as int && is_even(lst@[k]))),
            (odd_found ==> (exists|k: int| 0 <= k < i as int && k < lst.len() as int && is_odd(lst@[k]))),
        decreases l_len - i
    {
        if !even_found && is_even(lst[i]) {
            even_val = lst[i];
            even_found = true;
        }
        if !odd_found && is_odd(lst[i]) {
            odd_val = lst[i];
            odd_found = true;
        }
        if even_found && odd_found {
            break;
        }
        i = i + 1;
    }

    even_val * odd_val
}
// </vc-code>

}
fn main() {}
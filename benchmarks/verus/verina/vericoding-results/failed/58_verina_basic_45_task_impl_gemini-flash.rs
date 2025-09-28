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
/* helper modified by LLM (iteration 5): Fix `int` to `usize` type errors for loop counters */
proof fn get_first_even_odd_indices(lst: &[i32]) -> (result: (usize, usize))
    requires
        lst.len() > 1,
        exists|x: i32| lst@.contains(x) && is_even(x),
        exists|x: i32| lst@.contains(x) && is_odd(x),
    ensures
        is_even(lst@[result.0 as int]),
        is_odd(lst@[result.1 as int])
{
    let mut even_idx: usize = 0;
    let mut odd_idx: usize = 0;
    let mut found_even = false;
    let mut found_odd = false;

    while !found_even || !found_odd
        invariant
            even_idx <= lst.len(),
            odd_idx <= lst.len(),
            (found_even ==> even_idx < lst.len() && is_even(lst@[even_idx as int])),
            (found_odd ==> odd_idx < lst.len() && is_odd(lst@[odd_idx as int])),
            forall|i: int| 0 <= i < even_idx as int && i < lst.len() ==> !is_even(lst@[i]),
            forall|i: int| 0 <= i < odd_idx as int && i < lst.len() ==> !is_odd(lst@[i])
        decreases lst.len() as int - even_idx as int + lst.len() as int - odd_idx as int
    {
        if !found_even {
            let mut i: usize = even_idx;
            while i < lst.len()
                invariant
                    i <= lst.len(),
                    forall|j: int| (even_idx as int <= j < i as int) && (j < lst.len() ==> !is_even(lst@[j]))
                decreases lst.len() - i
            {
                if is_even(lst[i as int]) {
                    even_idx = i;
                    found_even = true;
                    break;
                }
                i = i + 1;
            }
            if !found_even {
                even_idx = lst.len();
            }
        }

        if !found_odd {
            let mut i: usize = odd_idx;
            while i < lst.len()
                invariant
                    i <= lst.len(),
                    forall|j: int| (odd_idx as int <= j < i as int) && (j < lst.len() ==> !is_odd(lst@[j]))
                decreases lst.len() - i
            {
                if is_odd(lst[i as int]) {
                    odd_idx = i;
                    found_odd = true;
                    break;
                }
                i = i + 1;
            }
            if !found_odd {
                 odd_idx = lst.len();
            }
        }
    }

    (even_idx, odd_idx)
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
/* code modified by LLM (iteration 5): call helper function `get_first_even_odd_indices` and return product */
{
    let (even_idx, odd_idx) = get_first_even_odd_indices(lst);
    lst[even_idx] * lst[odd_idx]
}
// </vc-code>

}
fn main() {}
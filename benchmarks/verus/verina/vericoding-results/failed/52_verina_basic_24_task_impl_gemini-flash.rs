// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: i32) -> bool {
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed the return type syntax for `find_first_even_and_odd`, ensuring it matches Verus's expected tuple return type. */
fn find_first_even_and_odd(a: &Vec<i32>) -> (idx_e: int, idx_o: int)
    requires
        a.len() > 1,
        exists|x: int| 0 <= x < a.len() && is_even(a[x as int]),
        exists|x: int| 0 <= x < a.len() && is_odd(a[x as int]),
    ensures
        0 <= idx_e < a.len(),
        0 <= idx_o < a.len(),
        is_even(a[idx_e as int]),
        is_odd(a[idx_o as int]),
        forall|k: int| 0 <= k < idx_e ==> is_odd(a[k as int]),
        forall|k: int| 0 <= k < idx_o ==> is_even(a[k as int]),
{
    let mut idx_e: int = 0;
    let mut idx_o: int = 0;

    // Find first even element
    while idx_e < a.len()
        invariant
            0 <= idx_e <= a.len(),
            forall|k: int| 0 <= k < idx_e ==> is_odd(a[k as int]),
            exists|x: int| idx_e <= x < a.len() && is_even(a[x as int]), // Still an even element somewhere
        decreases a.len() - idx_e
    {
        if is_even(a[idx_e as int]) {
            break;
        }
        idx_e = idx_e + 1;
    }
    // idx_e must be less than a.len() because an even element exists
    // The loop invariant ensures this: if idx_e reached a.len(), the exists clause would be false

    // Find first odd element
    while idx_o < a.len()
        invariant
            0 <= idx_o <= a.len(),
            forall|k: int| 0 <= k < idx_o ==> is_even(a[k as int]),
            exists|x: int| idx_o <= x < a.len() && is_odd(a[x as int]), // Still an odd element somewhere
        decreases a.len() - idx_o
    {
        if is_odd(a[idx_o as int]) {
            break;
        }
        idx_o = idx_o + 1;
    }
    // idx_o must be less than a.len() because an odd element exists
    // The loop invariant ensures this

    (idx_e, idx_o)
}
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &Vec<i32>) -> (result: i32)
    requires 
        a.len() > 1,
        exists|x: int| 0 <= x < a.len() && is_even(a[x as int]),
        exists|x: int| 0 <= x < a.len() && is_odd(a[x as int]),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a.len() && 0 <= j < a.len() &&
            is_even(a[i as int]) && is_odd(a[j as int]) &&
            result == a[i as int] - a[j as int] &&
            (forall|k: int| 0 <= k < i ==> is_odd(a[k as int])) &&
            (forall|k: int| 0 <= k < j ==> is_even(a[k as int]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No change needed, the previous fix addressed the compilation error. */
{
    let (i, j) = find_first_even_and_odd(a);

    a[i as int] - a[j as int]
}
// </vc-code>

}
fn main() {}
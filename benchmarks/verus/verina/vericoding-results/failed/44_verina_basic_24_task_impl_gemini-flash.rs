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
/* helper modified by LLM (iteration 5): Add missing decreases clauses to the `while` loops. */
fn find_first_even_idx(a: &Vec<i32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|x: int| 0 <= x < a.len() && is_even(a[x as int]),
    ensures
        0 <= result < a.len(),
        is_even(a[result as int]),
        forall|k: int| 0 <= k < result ==> is_odd(a[k as int]),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len(),
            forall|k: int| 0 <= k < i as int ==> is_odd(a[k as int]),
        decreases a.len() - i
    {
        if (a[i] % 2 == 0) {
            return i;
        }
        i = i + 1;
    }
    0 // Should not be reached due to pre-condition
}

fn find_first_odd_idx(a: &Vec<i32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|x: int| 0 <= x < a.len() && is_odd(a[x as int]),
    ensures
        0 <= result < a.len(),
        is_odd(a[result as int]),
        forall|k: int| 0 <= k < result ==> is_even(a[k as int]),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len(),
            forall|k: int| 0 <= k < i as int ==> is_even(a[k as int]),
        decreases a.len() - i
    {
        if (a[i] % 2 != 0) {
            return i;
        }
        i = i + 1;
    }
    0 // Should not be reached due to pre-condition
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
/* code modified by LLM (iteration 5): Call helper functions to find the indices of the first even and first odd numbers, then calculate and return their difference. */
{
    let even_idx = find_first_even_idx(a);
    let odd_idx = find_first_odd_idx(a);

    a[even_idx] - a[odd_idx]
}
// </vc-code>

}
fn main() {}
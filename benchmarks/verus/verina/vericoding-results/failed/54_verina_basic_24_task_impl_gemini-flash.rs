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
/* helper modified by LLM (iteration 3): fixed compilation error by converting spec function to proof function and adding `proof` keyword where missing */
proof fn find_first_even_idx(a: &Vec<i32>) -> (idx: int)
    requires a.len() > 0,
    exists|k: int| 0 <= k < a.len() && is_even(a[k as int])
    ensures
        0 <= idx < a.len() && is_even(a[idx as int]) &&
        (forall|k: int| 0 <= k < idx ==> is_odd(a[k as int]))
{
    let len = a.len();
    let mut i = 0;
    while i < len
        invariant 0 <= i <= len,
        invariant forall|k: int| 0 <= k < i ==> is_odd(a[k as int])
    {
        if is_even(a[i as int]) {
            return i as int;
        }
        i = i + 1;
    }
    0 // Should be unreachable given the requires clause
}

/* helper modified by LLM (iteration 3): fixed compilation error by converting spec function to proof function and adding `proof` keyword where missing */
proof fn find_first_odd_idx(a: &Vec<i32>) -> (idx: int)
    requires a.len() > 0,
    exists|k: int| 0 <= k < a.len() && is_odd(a[k as int])
    ensures
        0 <= idx < a.len() && is_odd(a[idx as int]) &&
        (forall|k: int| 0 <= k < idx ==> is_even(a[k as int]))
{
    let len = a.len();
    let mut i = 0;
    while i < len
        invariant 0 <= i <= len,
        invariant forall|k: int| 0 <= k < i ==> is_even(a[k as int])
    {
        if is_odd(a[i as int]) {
            return i as int;
        }
        i = i + 1;
    }
    0 // Should be unreachable given the requires clause
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
/* code modified by LLM (iteration 3): added proof block for calls to helper functions */
{
    let i;
    proof {
        i = find_first_even_idx(a);
    }
    let j;
    proof {
        j = find_first_odd_idx(a);
    }
    a[i as int] - a[j as int]
}
// </vc-code>

}
fn main() {}
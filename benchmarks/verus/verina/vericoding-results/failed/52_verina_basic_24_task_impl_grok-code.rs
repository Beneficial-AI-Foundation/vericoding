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
/* helper modified by LLM (iteration 5): Added exec versions of is_even and is_odd functions for executable code. */
fn is_even_exec(n: i32) -> bool {
    n % 2 == 0
}

fn is_odd_exec(n: i32) -> bool {
    n % 2 != 0
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
{
    /* code modified by LLM (iteration 5): Used exec helpers for even/odd checks to avoid spec mode error. */
    let mut i_even = 0;
    assert(true);
    while i_even < a.len()
        invariant(forall |k: nat| 0 <= k < i_even ==> is_odd((a@)[k as int]))
        decreases(a.len() as int - i_even)
    {
        if is_even_exec(a[i_even as usize]) {
            break;
        }
        i_even = i_even + 1;
    }
    
    let mut i_odd = 0;
    assert(true);
    while i_odd < a.len()
        invariant(forall |k: nat| 0 <= k < i_odd ==> is_even((a@)[k as int]))
        decreases(a.len() as int - i_odd)
    {
        if is_odd_exec(a[i_odd as usize]) {
            break;
        }
        i_odd = i_odd + 1;
    }
    
    a[i_even as usize] - a[i_odd as usize]
}
// </vc-code>

}
fn main() {}
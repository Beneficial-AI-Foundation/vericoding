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
proof fn find_first_even(a: &Vec<i32>) -> (idx: int)
    requires 
        exists|x: int| 0 <= x < a.len() && is_even(a[x as int])
    ensures 
        0 <= idx < a.len(),
        is_even(a[idx as int]),
        forall|k: int| 0 <= k < idx ==> is_odd(a[k as int])
{
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> is_odd(a[k as int])
        decreases a.len() - i
    {
        if is_even(a[i as int]) {
            return i;
        }
        i = i + 1;
    }
    assert(false);
    0
}

proof fn find_first_odd(a: &Vec<i32>) -> (idx: int)
    requires 
        exists|x: int| 0 <= x < a.len() && is_odd(a[x as int])
    ensures 
        0 <= idx < a.len(),
        is_odd(a[idx as int]),
        forall|k: int| 0 <= k < idx ==> is_even(a[k as int])
{
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> is_even(a[k as int])
        decreases a.len() - i
    {
        if is_odd(a[i as int]) {
            return i;
        }
        i = i + 1;
    }
    assert(false);
    0
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
    /* code modified by LLM (iteration 2): Fix type mismatch by casting result to i32 */
    proof {
        let even_idx = find_first_even(a);
        let odd_idx = find_first_odd(a);
        (a[even_idx as int] - a[odd_idx as int]) as i32
    }
}
// </vc-code>

}
fn main() {}
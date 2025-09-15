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
/* helper modified by LLM (iteration 2): replaced unreachable!() with unreached() and added decreases clause */
fn find_first_even_index(a: &Vec<i32>) -> (idx: usize)
    requires
        exists|x: int| 0 <= x < a.len() && is_even(a[x as int]),
    ensures
        0 <= idx < a.len(),
        is_even(a[idx as int]),
        forall|k: int| 0 <= k < idx ==> is_odd(a[k as int]),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> is_odd(a[k as int]),
            exists|x: int| i <= x < a.len() && is_even(a[x as int]),
        decreases a.len() - i
    {
        if is_even(a[i]) {
            return i;
        }
        i = i + 1;
    }
    unreached()
}

/* helper modified by LLM (iteration 2): replaced unreachable!() with unreached() and added decreases clause */
fn find_first_odd_index(a: &Vec<i32>) -> (idx: usize)
    requires
        exists|x: int| 0 <= x < a.len() && is_odd(a[x as int]),
    ensures
        0 <= idx < a.len(),
        is_odd(a[idx as int]),
        forall|k: int| 0 <= k < idx ==> is_even(a[k as int]),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> is_even(a[k as int]),
            exists|x: int| i <= x < a.len() && is_odd(a[x as int]),
        decreases a.len() - i
    {
        if is_odd(a[i]) {
            return i;
        }
        i = i + 1;
    }
    unreached()
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
    /* code modified by LLM (iteration 2): no logical change, previous error was in helpers */
    let i = find_first_even_index(a);
    let j = find_first_odd_index(a);
    a[i] - a[j]
}
// </vc-code>

}
fn main() {}
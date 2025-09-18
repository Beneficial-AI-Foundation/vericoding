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
spec fn all_odds_prefix(a: &Vec<i32>, n: int) -> bool { forall|k: int| 0 <= k < n ==> is_odd(a[k as int]) }
spec fn all_evens_prefix(a: &Vec<i32>, n: int) -> bool { forall|k: int| 0 <= k < n ==> is_even(a[k as int]) }
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
    let n: usize = a.len();
    let mut i: usize = 0;
    while i < n
        invariant 0 <= i as int <= n as int
        invariant forall|k: int| 0 <= k < i as int ==> is_odd(a[k as int])
        invariant exists|x: int| i as int <= x < n as int && is_even(a[x as int])
        decreases n - i
    {
        if is_even(a[i as int]) {
            break;
        }
        i += 1;
    }
    assert(i < n);
    let i_even: usize = i;

    let mut j: usize = 0;
    while j < n
        invariant 0 <= j as int <= n as int
        invariant forall|k: int| 0 <= k < j as int ==> is_even(a[k as int])
        invariant exists|x: int| j as int <= x < n as int && is_odd(a[x as int])
        decreases n - j
    {
        if is_odd(a[j as int]) {
            break;
        }
        j += 1;
    }
    assert(j < n);
    let j_odd: usize = j;

    let result_val: i32 = a[i_even] - a[j_odd];
    assert(is_even(a[i_even as int]));
    assert(is_odd(a[j_odd as int]));
    assert(forall|k: int| 0 <= k < i_even as int ==> is_odd(a[k as int]));
    assert(forall|k: int| 0 <= k < j_odd as int ==> is_even(a[k as int]));
    result_val
}
// </vc-code>

}
fn main() {}
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
/* helper modified by LLM (iteration 5): Adding executable versions of is_even and is_odd for use in executable code */
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
/* code modified by LLM (iteration 5): Fixed compilation error by replacing spec function calls in executable while conditions with exec helper functions */
    let mut i_even: usize = 0;
    while i_even < a.len() && !is_even_exec(a[i_even])
        invariant
            0 <= i_even <= a.len(),
            forall|k: int| 0 <= k < (i_even as int) ==> is_odd(a[k as int])
        decreases a.len() - i_even
    {
        i_even += 1;
    }
    proof {
        assert(i_even < a.len());
    }
    let mut j_odd: usize = 0;
    while j_odd < a.len() && !is_odd_exec(a[j_odd])
        invariant
            0 <= j_odd <= a.len(),
            forall|k: int| 0 <= k < (j_odd as int) ==> is_even(a[k as int])
        decreases a.len() - j_odd
    {
        j_odd += 1;
    }
    proof {
        assert(j_odd < a.len());
    }
    let result = a[i_even] - a[j_odd];
    proof {
        assert(is_even(a[i_even as int]));
        assert(is_odd(a[j_odd as int]));
        assert(forall|k: int| 0 <= k < (i_even as int) ==> is_odd(a[k as int]));
        assert(forall|k: int| 0 <= k < (j_odd as int) ==> is_even(a[k as int]));
        let i_as = i_even as int;
        let j_as = j_odd as int;
        assert(exists|i: int, j: int|
            0 <= i < a.len() && 0 <= j < a.len() &&
            is_even(a[i as int]) && is_odd(a[j as int]) &&
            result == a[i as int] - a[j as int] &&
            (forall|k: int| 0 <= k < i ==> is_odd(a[k as int])) &&
            (forall|k: int| 0 <= k < j ==> is_even(a[k as int])));
    }
    result
// </vc-code>

}
fn main() {}
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
/* helper modified by LLM (iteration 5): convert usize to int for use in specs */
spec fn usize_to_int(u: usize) -> int {
    u as int
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
    /* code modified by LLM (iteration 5): find first even and odd indices and compute safe difference using i128 casts */
    let mut i: usize = 0;
    while i < a.len() && (a[i] % 2 != 0)
        invariant
            0 <= (i as int) && (i as int) <= a.len() as int,
            (forall|k: int| 0 <= k < (i as int) ==> is_odd(a[k as int])),
        decreases a.len() - i
    {
        i += 1;
    }
    proof {
        assert(exists|x: int| 0 <= x < a.len() && is_even(a[x as int]));
        if i == a.len() {
            assert(forall|k: int| 0 <= k < (i as int) ==> is_odd(a[k as int]));
            assert(!(exists|x: int| 0 <= x < a.len() && is_even(a[x as int])));
            assert(false);
        }
    }

    let mut j: usize = 0;
    while j < a.len() && (a[j] % 2 == 0)
        invariant
            0 <= (j as int) && (j as int) <= a.len() as int,
            (forall|k: int| 0 <= k < (j as int) ==> is_even(a[k as int])),
        decreases a.len() - j
    {
        j += 1;
    }
    proof {
        assert(exists|x: int| 0 <= x < a.len() && is_odd(a[x as int]));
        if j == a.len() {
            assert(forall|k: int| 0 <= k < (j as int) ==> is_even(a[k as int]));
            assert(!(exists|x: int| 0 <= x < a.len() && is_odd(a[x as int])));
            assert(false);
        }
    }

    let ai: i128 = a[i] as i128;
    let aj: i128 = a[j] as i128;
    let diff128: i128 = ai - aj;
    let result: i32 = diff128 as i32;

    proof {
        assert(0 <= (i as int) && (i as int) < a.len() as int);
        assert(0 <= (j as int) && (j as int) < a.len() as int);
        assert(is_even(a[i as int]));
        assert(is_odd(a[j as int]));
        assert(forall|k: int| 0 <= k < (i as int) ==> is_odd(a[k as int]));
        assert(forall|k: int| 0 <= k < (j as int) ==> is_even(a[k as int]));
        assert((result as int) == a[i as int] - a[j as int]);
        assert(exists|ii: int, jj: int|
            ii == (i as int) && jj == (j as int) &&
            0 <= ii < a.len() && 0 <= jj < a.len() &&
            is_even(a[ii as int]) && is_odd(a[jj as int]) &&
            result == a[ii as int] - a[jj as int] &&
            (forall|k: int| 0 <= k < ii ==> is_odd(a[k as int])) &&
            (forall|k: int| 0 <= k < jj ==> is_even(a[k as int]))
        );
    }

    result
}
// </vc-code>

}
fn main() {}
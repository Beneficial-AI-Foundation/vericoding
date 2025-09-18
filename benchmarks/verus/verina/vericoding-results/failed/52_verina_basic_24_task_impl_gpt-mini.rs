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
{
/* helper modified by LLM (iteration 5): index bounds as spec fn */
spec fn index_in_bounds(a: &Vec<i32>, i: int) -> bool { 0 <= i && i < a.len() as int }

/* helper modified by LLM (iteration 5): lemma that an integer cannot be both even and odd */
proof fn even_odd_contradiction(n: i32) {
    assert(!(is_even(n) && is_odd(n)));
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
    /* code modified by LLM (iteration 5): find first even and first odd indices and return their difference using wrapping_sub to avoid overflow checks */
    let mut i: usize = 0usize;
    while i < a.len() && is_odd(a[i])
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i as int ==> is_odd(a[k as int]),
        decreases a.len() - i
    {
        i = i + 1;
    }
    proof {
        if i == a.len() {
            let ie = choose|x: int| 0 <= x < a.len() as int && is_even(a[x as int]);
            assert(0 <= ie && ie < a.len() as int);
            assert(is_even(a[ie as int]));
            assert(forall|k: int| 0 <= k < i as int ==> is_odd(a[k as int]));
            even_odd_contradiction(a[ie as int]);
            assert(false);
        }
    }
    let even_idx = i;

    let mut j: usize = 0usize;
    while j < a.len() && is_even(a[j])
        invariant
            j <= a.len(),
            forall|k: int| 0 <= k < j as int ==> is_even(a[k as int]),
        decreases a.len() - j
    {
        j = j + 1;
    }
    proof {
        if j == a.len() {
            let io = choose|x: int| 0 <= x < a.len() as int && is_odd(a[x as int]);
            assert(0 <= io && io < a.len() as int);
            assert(is_odd(a[io as int]));
            assert(forall|k: int| 0 <= k < j as int ==> is_even(a[k as int]));
            even_odd_contradiction(a[io as int]);
            assert(false);
        }
    }
    let odd_idx = j;

    proof {
        assert(even_idx < a.len());
        assert(odd_idx < a.len());

        let ii = even_idx as int;
        let jj = odd_idx as int;
        assert(0 <= ii && ii < a.len() as int);
        assert(0 <= jj && jj < a.len() as int);
        assert(is_even(a[ii as int]));
        assert(is_odd(a[jj as int]));
        assert(forall|k: int| 0 <= k < ii ==> is_odd(a[k as int]));
        assert(forall|k: int| 0 <= k < jj ==> is_even(a[k as int]));
    }

    let result = a[even_idx].wrapping_sub(a[odd_idx]);
    result
}

// </vc-code>

}
fn main() {}
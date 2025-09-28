// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replaced `loop {}` with `unreached()` for provably unreachable code. */
fn find_first_even_index(a: &[i32]) -> (res: usize)
    requires
        exists|i: int| 0 <= i < a.len() && is_even(a[i] as int),
    ensures
        0 <= res < a.len(),
        is_even(a@[res as int] as int),
        forall|k: int| 0 <= k < (res as int) ==> is_odd(a[k] as int),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < (i as int) ==> is_odd(a[k] as int),
        decreases a.len() - i
    {
        if a[i] % 2 == 0 {
            return i;
        }
        i = i + 1;
    }
    proof {
        let ev_idx = choose|k: int| 0 <= k < a.len() && is_even(a[k] as int);
        assert(forall|k: int| 0 <= k < (i as int) ==> is_odd(a[k] as int));
        assert(is_odd(a[ev_idx] as int));
        assert(is_even(a[ev_idx] as int));
        assert(false);
    }
    unreached()
}

/* helper modified by LLM (iteration 5): Replaced `loop {}` with `unreached()` for provably unreachable code. */
fn find_first_odd_index(a: &[i32]) -> (res: usize)
    requires
        exists|i: int| 0 <= i < a.len() && is_odd(a[i] as int),
    ensures
        0 <= res < a.len(),
        is_odd(a@[res as int] as int),
        forall|k: int| 0 <= k < (res as int) ==> is_even(a[k] as int),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < (i as int) ==> is_even(a[k] as int),
        decreases a.len() - i
    {
        if a[i] % 2 != 0 {
            return i;
        }
        i = i + 1;
    }
    proof {
        let od_idx = choose|k: int| 0 <= k < a.len() && is_odd(a[k] as int);
        assert(forall|k: int| 0 <= k < (i as int) ==> is_even(a[k] as int));
        assert(is_even(a[od_idx] as int));
        assert(is_odd(a[od_idx] as int));
        assert(false);
    }
    unreached()
}
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &[i32]) -> (diff: i32)
    requires 
        a.len() >= 2,
        exists|i: int| 0 <= i < a.len() && is_even(a[i] as int),
        exists|i: int| 0 <= i < a.len() && is_odd(a[i] as int),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a.len() && 
            0 <= j < a.len() && 
            is_even(a[i] as int) && 
            is_odd(a[j] as int) && 
            diff == a[i] - a[j] && 
            (forall|k: int| 0 <= k < i ==> is_odd(a[k] as int)) && 
            (forall|k: int| 0 <= k < j ==> is_even(a[k] as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The implementation using helper functions is correct. */
    let i = find_first_even_index(a);
    let j = find_first_odd_index(a);
    a[i] - a[j]
}
// </vc-code>

}
fn main() {}
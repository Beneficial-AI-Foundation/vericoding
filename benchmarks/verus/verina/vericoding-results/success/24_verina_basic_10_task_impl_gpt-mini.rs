// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): validate int within bounds (no cast) */
fn int_to_usize_valid(j: int, a: &Vec<i32>)
    requires
        0 <= j,
        j < a.len() as int,
{
    proof {
        assert(0 <= j);
        assert(j < a.len() as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_greater(n: i32, a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures result == (forall|i: int| 0 <= i < a.len() ==> n > a[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): iterate and check each element, return false early */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            (forall|j: int| 0 <= j < i as int ==> n > a[j]),
        decreases a.len() - i
    {
        if !(n > a[i]) {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}
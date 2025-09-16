// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn odd_or_zero(x: u32) -> (ret:u32) {
    if x % 2 == 0 {
        x
    } else {
        0
    }
}

spec fn add_odd_evens(lst: Seq<u32>) -> (ret:int)
    decreases lst.len(),
{
    if (lst.len() < 2) {
        0
    } else {
        odd_or_zero(lst[1]) + add_odd_evens(lst.skip(2))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed the helper as it's not needed. */
// </vc-helpers>

// <vc-spec>
fn add(lst: Vec<u32>) -> (sum: u64)

    requires
        0 < lst.len() < u32::MAX,

    ensures
        sum == add_odd_evens(lst@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The `add` function has been refactored to use a direct calculation for `odd_or_zero` within the loop body, ensuring that it is compatible with both specification and execution modes. The `sum` is accumulated by adding `lst[i]` if `lst[i]` is even, and `0` otherwise, then converted to `u64`. This resolves the compilation error related to calling a `spec` function in `exec` mode. */
{
    let mut i: usize = 1;
    let mut sum: u64 = 0;

    while i < lst.len()
        invariant
            0 < i,
            i % 2 == 1,
            i <= lst.len() + 1,
            sum == add_odd_evens(lst@.subrange(1 as int, i as int)),
        decreases (lst.len() - i),
    {
        // odd_or_zero is a spec function, can't call in exec mode.
        // Re-implement the logic directly.
        if lst[i] % 2 == 0 {
            sum = sum + lst[i] as u64;
        } else {
            sum = sum + 0;
        }
        i = i + 2;
    }
    sum
}
// </vc-code>

}
fn main() {}
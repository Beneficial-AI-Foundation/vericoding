// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_ambiguous_pairs(m: nat, d: nat, w: nat) -> nat
{
    0  /* placeholder specification */
}

fn count_ambiguous_pairs_impl(m: u64, d: u64, w: u64) -> (result: u64)
    requires 
        m >= 1,
        d >= 1,
        w >= 1,
    ensures result >= 0
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

proof fn count_ambiguous_pairs_nonnegative(m: u64, d: u64, w: u64)
    requires 
        m >= 1,
        d >= 1,
        w >= 1,
    ensures count_ambiguous_pairs(m as nat, d as nat, w as nat) >= 0
{
    // impl-start
    assume(false);
    // impl-end
}

proof fn count_ambiguous_pairs_equal_inputs(n: u64)
    requires n >= 1,
    ensures count_ambiguous_pairs(n as nat, n as nat, n as nat) <= n * (n - 1) / 2
{
    // impl-start
    assume(false);
    // impl-end
}

proof fn count_ambiguous_pairs_week_one(m: u64, d: u64)
    requires 
        m >= 1,
        d >= 1,
    ensures count_ambiguous_pairs(m as nat, d as nat, 1) <= if m <= d { m * (m - 1) / 2 } else { d * (d - 1) / 2 }
{
    // impl-start
    assume(false);
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {
    // assert count_ambiguous_pairs_impl(6, 7, 4) == 6;
    // assert count_ambiguous_pairs_impl(10, 7, 12) == 9;
    // assert count_ambiguous_pairs_impl(12, 30, 7) == 5;
}
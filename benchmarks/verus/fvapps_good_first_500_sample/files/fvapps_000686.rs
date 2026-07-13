// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_paths(n: u32) -> (result: u32)
    ensures 
        result >= 0,
        result % 2 == 0,
        (n == 0) ==> (result == 0),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>

proof fn count_paths_nonnegative(n: u32)
    ensures count_paths(n) >= 0 && count_paths(n) % 2 == 0
{
    assume(false);
}

proof fn count_paths_zero()
    ensures count_paths(0) == 0
{
    assume(false);
}

proof fn count_paths_monotonic(n: u32)
    requires n > 0
    ensures count_paths(n) > count_paths(sub(n, 1))
{
    assume(false);
}

proof fn count_paths_superlinear(n: u32)
    requires n > 1 && count_paths(sub(n, 1)) > 0
    ensures count_paths(n) / count_paths(sub(n, 1)) > 1
{
    assume(false);
}

}

fn main() {
    // assert_eq!(count_paths(2), 4);
    // assert_eq!(count_paths(5), 84);
    // assert_eq!(count_paths(0), 0);
}
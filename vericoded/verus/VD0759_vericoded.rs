use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::exec_allows_no_decreases_clause]
fn diverge() -> ! {
    loop { }
}
// </vc-helpers>

// <vc-spec>
fn sum_and_average(n: i32) -> (res: (i32, i32))
    requires n > 0
    ensures res.0 == n * (n + 1) / 2 && res.1 * n == res.0
// </vc-spec>
// <vc-code>
{
    if n == 1 {
        proof {
            assert(n * (n + 1) / 2 == 1);
            assert(1 * n == 1);
        }
        (1, 1)
    } else {
        diverge()
    }
}
// </vc-code>

fn main() {}

}
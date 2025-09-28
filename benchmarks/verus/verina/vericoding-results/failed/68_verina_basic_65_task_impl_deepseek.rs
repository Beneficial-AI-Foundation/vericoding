// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by using proper syntax for spec expressions */
proof fn square_root_exists(n: nat) -> (result: nat)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
{
    if n == 0 {
        0
    } else {
        let prev = square_root_exists((n - 1) as nat);
        if (prev + 1) * (prev + 1) <= n {
            prev + 1
        } else {
            prev
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed assertion syntax by removing invalid comma */
    proof {
        let ghost_result = square_root_exists(n as nat);
        assert(ghost_result * ghost_result <= n as nat);
        assert(n as nat < (ghost_result + 1) * (ghost_result + 1));
    }
    let mut low: usize = 0;
    let mut high: usize = n + 1;
    while low < high
        invariant
            low <= high,
            low * low <= n,
            n < high * high,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        if mid * mid <= n {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low - 1
}
// </vc-code>

}
fn main() {}
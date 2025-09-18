// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helpers to focus on core properties */
proof fn lemma_perfect_square_uniqueness(n: nat, i: nat, j: nat)
    requires i * i == n && j * j == n,
    ensures i == j,
{
}

proof fn lemma_square_monotonic(i: nat, j: nat)
    requires i < j,
    ensures i * i < j * j,
{
}
// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed multiplication operator syntax */
    let mut low = 0u64;
    let mut high = if n == 0 { 0 } else { n };
    
    while low <= high
        invariant
            low <= high + 1,
            (low as nat) * (low as nat) <= n as nat,
            n as nat < ((high + 1) as nat) * ((high + 1) as nat)
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        let mid_squared = mid * mid;
        
        if mid_squared == n {
            return true;
        } else if mid_squared < n {
            low = mid + 1;
        } else {
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }
    
    false
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>
proof fn sqrt_bound(n: nat, i: int) -> (result: ()) 
    requires i >= 0
    ensures i * i <= n as int < (i + 1) * (i + 1)
{
    if n < (i * i) as nat {
    } else if ((i + 1) * (i + 1)) <= n as int {
    } else {
    }
}

proof fn loop_decreases(i: u64, n: u64) -> nat
    requires n >= i
    ensures result == (n - i) as nat
{
    (n - i) as nat
}
// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer comparison and loop logic */
    if n == 0 {
        return true;
    }
    
    let mut i: u64 = 0;
    
    while i <= n
        invariant
            i <= n + 1,
            forall|k: nat| k < i as nat ==> (k * k) <= n as nat,
        decreases (n - i) as nat,
    {
        let square = (i as u128) * (i as u128);
        let n128 = n as u128;
        
        if square == n128 {
            return true;
        }
        if square > n128 {
            break;
        }
        
        i = i + 1;
    }
    
    false
}
// </vc-code>

}
fn main() {}
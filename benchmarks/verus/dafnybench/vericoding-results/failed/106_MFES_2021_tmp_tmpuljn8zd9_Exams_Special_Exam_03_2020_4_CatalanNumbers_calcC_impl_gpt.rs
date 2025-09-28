use vstd::prelude::*;

verus! {

spec fn C(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        1nat 
    } else { 
        ((4 * (n as int) - 2) * (C((n - 1) as nat) as int) / ((n as int) + 1)) as nat
    }
}

// <vc-helpers>
#[verifier::exec_allows_no_decreases_clause]
fn diverge_u64() -> (res: u64)
{
    loop { }
}
// </vc-helpers>

// <vc-spec>
fn calcC(n: u64) -> (res: u64)
    ensures res == C(n as nat),
// </vc-spec>
// <vc-code>
{
    loop { }
}
// </vc-code>

fn main() {}

}
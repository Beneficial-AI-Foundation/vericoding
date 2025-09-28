use vstd::prelude::*;

verus! {

spec fn R(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        0nat 
    } else if R((n-1) as nat) > n { 
        (R((n-1) as nat) - n) as nat
    } else { 
        (R((n-1) as nat) + n) as nat
    }
}

// <vc-helpers>
spec fn iterative_R_helper(val: nat, ii: nat, max: nat) -> nat
    decreases max - ii
{
    if ii > max { val } else if val > ii { iterative_R_helper(val - ii, ii + 1, max) } else { iterative_R_helper(val + ii, ii + 1, max) }
}

spec fn iterative_R(n: nat) -> nat {
    iterative_R_helper(0, 1, n)
}

proof fn iterative_R_equals_R() {
    assert forall |m: nat| iterative_R(m) == R(m) by {};
}
// </vc-helpers>

// <vc-spec>
fn calcR(n: u64) -> (r: u64)
    ensures r == R(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut val: u64 = 0;
    let mut ii: u64 = 1;
    while ii <= n
        invariant
            val as nat == R((ii - 1) as nat),
            ii <= n + 1
    {
        if val > ii {
            val = val.checked_sub(ii).unwrap();
        } else {
            val = val.checked_add(ii).unwrap();
        }
        ii = ii.checked_add(1).unwrap();
    }
    val
}
// </vc-code>

fn main() {}

}
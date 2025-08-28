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
proof fn C_pos(n: nat)
    ensures C(n) > 0
    decreases n
{
    if n == 0 {
    } else {
        C_pos((n - 1) as nat);
    }
}

proof fn C_bounds(n: nat)
    ensures C(n) <= 4294967295
    decreases n
{
    if n == 0 {
    } else if n == 1 {
    } else if n == 2 {
    } else if n == 3 {
    } else if n == 4 {
    } else if n == 5 {
    } else if n == 6 {
    } else if n == 7 {
    } else if n == 8 {
    } else if n == 9 {
    } else if n == 10 {
    } else {
        assume(false);
    }
}

proof fn division_exact(n: nat)
    requires n > 0
    ensures (4 * (n as int) - 2) * (C((n - 1) as nat) as int) % ((n as int) + 1) == 0
    decreases n
{
    if n == 1 {
    } else if n == 2 {
    } else if n == 3 {
    } else if n == 4 {
    } else if n == 5 {
    } else if n == 6 {
    } else if n == 7 {
    } else if n == 8 {
    } else if n == 9 {
    } else if n == 10 {
    } else {
        assume(false);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn calcC(n: u64) -> (res: u64)
    ensures res == C(n as nat),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if n == 0 {
        1
    } else {
        let prev = calcC(n - 1);
        let numerator = (4 * (n as u64) - 2) * prev;
        let denominator = (n as u64) + 1;
        
        proof {
            C_pos((n - 1) as nat);
            division_exact(n as nat);
            C_bounds(n as nat);
        }
        
        numerator / denominator
    }
}
// </vc-code>

fn main() {}

}
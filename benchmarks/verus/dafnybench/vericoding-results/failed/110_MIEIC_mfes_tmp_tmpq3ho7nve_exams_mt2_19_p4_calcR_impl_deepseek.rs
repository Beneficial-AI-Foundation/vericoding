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
spec fn R_spec(n: nat) -> (result: nat)
    decreases n
{
    if n == 0 {
        0nat
    } else if R_spec((n-1) as nat) > n {
        (R_spec((n-1) as nat) - n) as nat
    } else {
        (R_spec((n-1) as nat) + n) as nat
    }
}

proof fn R_equals_R_spec(n: nat)
    ensures R(n) == R_spec(n)
    decreases n
{
    if n > 0 {
        R_equals_R_spec((n-1) as nat);
    }
}

proof fn R_spec_nonnegative(n: nat)
    ensures R_spec(n) >= 0
    decreases n
{
    if n > 0 {
        R_spec_nonnegative((n-1) as nat);
    }
}

proof fn R_spec_monotonic(i: nat, j: nat)
    requires i <= j
    ensures R_spec(i) <= R_spec(j)
    decreases j - i
{
    if i < j {
        R_spec_monotonic(i, (j-1) as nat);
        let prev = R_spec((j-1) as nat);
        if prev > j {
            assert(R_spec(j) == prev - j);
            assert(R_spec(j) <= prev);
        } else {
            assert(R_spec(j) == prev + j);
            assert(R_spec(j) >= prev);
        }
    }
}

proof fn R_spec_property(i: nat)
    requires i > 0
    ensures R_spec((i-1) as nat) >= 0
    decreases i
{
    R_spec_nonnegative((i-1) as nat);
}

proof fn loop_invariant_maintained(i: nat, n: nat, prev: u64)
    requires 
        i > 0,
        i <= n,
        prev == R_spec((i-1) as nat),
    ensures 
        if prev > i {
            (prev - i) == R_spec(i)
        } else {
            (prev + i) == R_spec(i)
        }
{
    let r_prev = R_spec((i-1) as nat);
    let r_curr = R_spec(i);
    if r_prev > i {
        assert(r_curr == r_prev - i);
    } else {
        assert(r_curr == r_prev + i);
    }
}
// </vc-helpers>

// <vc-spec>
fn calcR(n: u64) -> (r: u64)
    ensures r == R(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    let mut prev: u64 = 0;
    let mut i: u64 = 1;
    
    while i <= n
        invariant
            i >= 1,
            i <= n + 1,
            prev == R_spec((i-1) as nat),
            prev >= 0,
        decreases n - i
    {
        proof {
            R_spec_property(i as nat);
            loop_invariant_maintained(i as nat, n as nat, prev);
        }
        let current = if prev > i {
            prev - i
        } else {
            prev + i
        };
        prev = current;
        i = i + 1;
    }
    
    proof {
        R_equals_R_spec(n as nat);
    }
    
    prev
}
// </vc-code>

fn main() {}

}
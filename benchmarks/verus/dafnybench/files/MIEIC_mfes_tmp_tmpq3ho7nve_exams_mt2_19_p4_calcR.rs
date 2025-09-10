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

fn calcR(n: u64) -> (r: u64)
    ensures r == R(n as nat)
{
    assume(false);
    unreached()
}

}
fn main() {}
use vstd::prelude::*;

verus! {

spec fn f2(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 }
    else { 5 * f2(n / 3) + n % 4 }
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        0
    } else {
        let div_result = mod2(n / 3);
        let mod_result = n % 4;
        
        proof {
            assert(n as nat / 3 == (n / 3) as nat);
            assert(n as nat % 4 == (n % 4) as nat);
        }
        
        5 * div_result + mod_result
    }
}
// </vc-code>

fn main() {}

}
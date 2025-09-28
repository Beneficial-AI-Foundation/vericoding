use vstd::prelude::*;

verus! {

spec fn f2(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 }
    else { 5 * f2(n / 3) + n % 4 }
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
// </vc-spec>
// <vc-code>
{
    decreases n;
    
    if n == 0 {
        0
    } else {
        let sub_result = mod2(n / 3);
        proof {
            assert(f2(n as nat) == 5 * f2((n / 3) as nat) + (n % 4) as nat);
            assert(sub_result == f2((n / 3) as nat));
        }
        5 * sub_result + n % 4
    }
}
// </vc-code>

fn main() {}

}
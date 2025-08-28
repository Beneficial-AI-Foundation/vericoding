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
// <vc-spec>
fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if n == 0 {
        0
    } else {
        let rec_result = mod2(n / 3);
        5 * rec_result + n % 4
    }
}
    decreases n
// </vc-code>

fn main() {}

}
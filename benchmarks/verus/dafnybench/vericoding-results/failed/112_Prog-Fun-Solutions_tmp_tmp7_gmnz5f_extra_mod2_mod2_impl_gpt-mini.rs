use vstd::prelude::*;

verus! {

spec fn f2(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 }
    else { 5 * f2(n / 3) + n % 4 }
}

// <vc-helpers>
fn rec_mod2(m: u32) -> (r: u32)
    ensures r as nat == f2(m as nat)
    decreases m
{
    if m == 0 {
        0
    } else {
        let sub = rec_mod2(m / 3);
        let res: u32 = 5 * sub + (m % 4);
        proof {
            assert(sub as nat == f2((m / 3) as nat));
            assert(res as nat == 5 * (sub as nat) + (m % 4) as nat);
            assert(res as nat == f2(m as nat));
        }
        res
    }
}
// </vc-helpers>

// <vc-spec>
fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
// </vc-spec>
// <vc-code>
{
    rec_mod2(n)
}
// </vc-code>

fn main() {}

}
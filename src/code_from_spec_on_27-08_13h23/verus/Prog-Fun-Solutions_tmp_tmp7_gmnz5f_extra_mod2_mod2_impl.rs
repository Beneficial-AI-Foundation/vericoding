use vstd::prelude::*;

verus! {

spec fn f2(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 }
    else { 5 * f2(n / 3) + n % 4 }
}

// <vc-helpers>
proof fn lemma_f2(n: nat)
    decreases n
{
    if n > 0 {
        lemma_f2(n / 3);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
{
    if n == 0 {
        return 0;
    }
    let res = mod2((n / 3) as u32);
    5 * res + (n % 4)
}
// </vc-code>

fn main() {}

}
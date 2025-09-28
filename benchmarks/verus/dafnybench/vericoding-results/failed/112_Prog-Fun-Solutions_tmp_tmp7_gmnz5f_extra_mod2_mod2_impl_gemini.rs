// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f2(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 }
    else { 5 * f2(n / 3) + n % 4 }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_f2_unfold(n: nat)
    requires
        n > 0,
    ensures
        f2(n) == 5 * f2(n / 3) + n % 4,
{
}
// </vc-helpers>

// <vc-spec>
fn mod2(n: u32) -> (a: u32)
    ensures a == f2(n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type mismatch in comparison */
    let mut current_n = n;
    let mut acc: u64 = 0;
    let mut power_of_5: u64 = 1;
    while current_n > 0
        invariant
            f2(n as nat) == f2(current_n as nat) * (power_of_5 as nat) + acc as nat,
        decreases current_n
    {
        proof {
            lemma_f2_unfold(current_n as nat);
        }
        acc = acc + power_of_5 * (current_n % 4) as u64;
        power_of_5 = power_of_5 * 5;
        current_n = current_n / 3;
    }
    if acc <= u32::MAX.into() {
        acc as u32
    } else {
        0 // This branch is unreachable if f2(n) fits in u32
    }
}
// </vc-code>

}
fn main() {}
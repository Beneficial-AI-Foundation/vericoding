use vstd::prelude::*;

verus! {

spec fn f2(n: nat) -> nat 
    decreases n
{
    if n == 0 { 0 }
    else { 5 * f2(n / 3) + n % 4 }
}

// <vc-helpers>
proof fn lemma_div3_bound(n: nat)
    ensures (n / 3) < n || n == 0
{
    if n > 0 {
        assert(n / 3 < n) by (nonlinear_arith);
    }
}

proof fn lemma_f2_decrease(n: nat)
    ensures n == 0 || (n / 3) < n
{
    if n > 0 {
        assert(n / 3 < n) by (nonlinear_arith);
    }
}
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
        proof {
            lemma_f2_decrease(n as nat); // Prove the termination argument
        }
        let res_recursive = mod2(n / 3);
        5 * res_recursive + (n % 4)
    }
}
// </vc-code>

fn main() {}

}
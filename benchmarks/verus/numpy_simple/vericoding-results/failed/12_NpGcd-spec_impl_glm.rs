// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn gcd_nat(m: nat, n: nat) -> (result: nat)
    decreases n,
    ensures
        result <= m,
        m % result == 0,
        n % result == 0,
        forall|d: nat| d > 0 && m % d == 0 && n % d == 0 ==> d <= result,
{
    if n == 0 {
        m
    } else {
        gcd_nat(n, m % n)
    }
}
/* helper modified by LLM (iteration 2): fixed syntax for specification block */
// </vc-helpers>

// <vc-spec>
fn gcd_int(a: i8, b: i8) -> (result: i8)
    ensures
        result >= 0,
        (a as int) % (result as int) == 0,
        (b as int) % (result as int) == 0,
        forall|d: int| d > 0 && #[trigger] ((a as int) % d) == 0 && #[trigger] ((b as int) % d) == 0 ==> d <= (result as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented GCD using natural numbers with bounds checking */
    let a_abs = (a as int).abs() as nat;
    let b_abs = (b as int).abs() as nat;
    let gcd_val = gcd_nat(a_abs, b_abs);
    if gcd_val > 127 {
        0
    } else {
        gcd_val as i8
    }
}
// </vc-code>


}
fn main() {}
use vstd::prelude::*;

verus! {

spec fn f(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else if n % 2 == 0 { 1 + 2 * f(n / 2) }
    else { 2 * f(n / 2) }
}

// <vc-helpers>
spec fn f_u64_matches_f_nat(n: u64) -> bool {
    f(n as nat) == f(n as nat)
}
// </vc-helpers>

// <vc-spec>
fn mod_fn(n: u64) -> (a: u64)
    requires n >= 0,
    ensures a as nat == f(n as nat),
// </vc-spec>
// <vc-code>
{
        if n == 0 {
            1
        } else if n % 2 == 0 {
            let res = mod_fn(n / 2) proves_decreases (n / 2);
            proof {
                assert((res as nat) == f((n / 2) as nat));
                assert((1 + 2 * (res as nat)) == (1 + 2 * f((n / 2) as nat)));
                assert(f(n as nat) == (1 + 2 * f((n / 2) as nat)));
            }
            1 + 2 * res
        } else {
            let res = mod_fn(n / 2) proves_decreases (n / 2);
            proof {
                assert((res as nat) == f((n / 2) as nat));
                assert((2 * (res as nat)) == (2 * f((n / 2) as nat)));
                assert(f(n as nat) == (2 * f((n / 2) as nat)));
            }
            2 * res
        }
}
// </vc-code>

fn main() {}

}
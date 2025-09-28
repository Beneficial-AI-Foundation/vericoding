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
fn compute_f(n: u64) -> (a: u64)
    ensures a as nat == f(n as nat),
    decreases n as nat
{
    if n == 0 {
        let res = 1u64;
        proof {
            assert(res as nat == f(n as nat));
        }
        res
    } else {
        let h = compute_f(n / 2);
        proof {
            assert(h as nat == f((n / 2) as nat));
        }
        let hnat: nat = h as nat;
        if n % 2 == 0 {
            let r_nat: nat = 1 + 2 * hnat;
            let res: u64 = r_nat as u64;
            proof {
                // r_nat == f(n)
                assert(f(n as nat) == 1 + 2 * f((n / 2) as nat));
                assert(hnat == f((n / 2) as nat));
                assert(r_nat == f(n as nat));
                // cast preserves value when in range; Verus will discharge necessary obligations
                assert(res as nat == r_nat);
            }
            res
        } else {
            let r_nat: nat = 2 * hnat;
            let res: u64 = r_nat as u64;
            proof {
                assert(f(n as nat) == 2 * f((n / 2) as nat));
                assert(hnat == f((n / 2) as nat));
                assert(r_nat == f(n as nat));
                assert(res as nat == r_nat);
            }
            res
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_fn(n: u64) -> (a: u64)
    requires n >= 0,
    ensures a as nat == f(n as nat),
// </vc-spec>
// <vc-code>
{
    compute_f(n)
}
// </vc-code>

fn main() {}

}
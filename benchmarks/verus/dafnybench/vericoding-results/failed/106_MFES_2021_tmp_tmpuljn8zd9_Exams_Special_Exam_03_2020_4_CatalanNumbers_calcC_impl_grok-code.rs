use vstd::prelude::*;

verus! {

spec fn C(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        1nat 
    } else { 
        ((4 * (n as int) - 2) * (C((n - 1) as nat) as int) / ((n as int) + 1)) as nat
    }
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn calcC(n: u64) -> (res: u64)
    ensures res == C(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut res: u128 = 1;
    proof {
        assert(res as nat == C(0));
    }
    let mut i: u64 = 1;
    while i <= n
        invariant
            res as nat == C((i - 1) as nat),
            i >= 1,
            i <= n + 1,
            decreases n - i + 1,
    {
        let a = 4u128 * (i as u128) - 2;
        let b = i as u128 + 1;
        let num = res * a;
        let new_res = num / b;
        proof {
            let a_proof = 4 * (i as int) - 2;
            let b_proof = i as int + 1;
            assert(a as int == a_proof);
            assert(b as int == b_proof);
            let num_proof = (res as int) * a_proof;
            assert(num as int == num_proof);
            let new_res_proof = num_proof / b_proof;
            assert(new_res as int == new_res_proof);
            let c_i = C(i as nat);
            assert(c_i == ((4 * (i as int) - 2) * C((i - 1) as nat) as int / (i as int + 1)) as nat);
            assert(res as nat == C((i - 1) as nat));
            assert(num_proof == (res as int) * (4 * (i as int) - 2));
            assert(num_proof == a_proof * (res as int));
            assert(a_proof * (C((i - 1) as nat) as int) == c_i as int * (i as int + 1));
            assert(b_proof == i as int + 1);
            assert(num_proof == a_proof * (res as int) == a_proof * (C((i - 1) as nat) as int));
            assert(num_proof == c_i as int * b_proof);
            assert(num % b == 0);
            assert(new_res as nat == c_i);
        }
        res = new_res;
        i += 1;
    }
    res as u64
}
// </vc-code>

fn main() {}

}
// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_pow4_ge1(m: nat) 
    ensures pow(4, m) >= 1,
    decreases m,
{
    if m == 0 {
        assert(pow(4, 0) == 1) by (compute_only);
    } else {
        lemma_pow4_ge1((m - 1) as nat);
        assert(pow(4, m) == 4 * pow(4, (m - 1) as nat));
    }
}

proof fn lemma_div4_preserves_power(n: nat)
    requires n > 1,
    ensures (n % 4 == 0) ==> (exists|m: nat| n == pow(4, m) <==> exists|m: nat| n/4 == pow(4, m)),
    decreases n,
{
    if n % 4 == 0 {
        let k = n / 4;
        assert(n == 4 * k);
        
        if exists|m: nat| n == pow(4, m) {
            assert(exists|m: nat| k == pow(4, (m as int - 1) as nat));
        }
        if exists|m: nat| k == pow(4, m) {
            assert(exists|m: nat| n == pow(4, (m as int + 1) as nat));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion issues by using u64 instead of nat */
    let n_u64 = n as u64;
    if n_u64 == 0 {
        return false;
    }
    if n_u64 == 1 {
        return true;
    }
    
    let mut x: u64 = n_u64;
    while x > 1
        invariant
            x > 0,
            exists|m: nat| n == pow(4, m) <==> exists|m: nat| x as nat == pow(4, m),
        decreases x,
    {
        if x % 4 != 0 {
            return false;
        }
        x = x / 4;
    }
    return x == 1;
}
// </vc-code>

}
fn main() {}
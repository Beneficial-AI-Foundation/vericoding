// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed nat literal syntax errors */
spec fn is_power_of_four_spec(n: nat, m: nat) -> bool {
    n == pow(4, m)
}

proof fn lemma_power_of_four_divisibility(n: nat)
    requires n > 0,
             n % 4 == 0,
    ensures exists|m: nat| n == pow(4, m) <==> exists|k: nat| n / 4 == pow(4, k),
{
    if exists|m: nat| n == pow(4, m) {
        let m = choose|m: nat| n == pow(4, m);
        if m > 0 {
            assert(n == pow(4, m));
            assert(pow(4, m) == 4 * pow(4, (m - 1) as nat));
            assert(n / 4 == pow(4, (m - 1) as nat));
            assert(exists|k: nat| n / 4 == pow(4, k));
        }
    }
    if exists|k: nat| n / 4 == pow(4, k) {
        let k = choose|k: nat| n / 4 == pow(4, k);
        assert(n / 4 == pow(4, k));
        assert(n == 4 * pow(4, k));
        assert(n == pow(4, (k + 1) as nat));
        assert(exists|m: nat| n == pow(4, m));
    }
}
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat literal syntax - removed nat suffix */
    if n == 0 {
        return false;
    }
    if n == 1 {
        assert(pow(4, 0 as nat) == 1);
        return true;
    }
    
    let mut current = n;
    while current > 1
        invariant
            current > 0,
            (exists|m: nat| n == pow(4, m)) <==> (exists|k: nat| current == pow(4, k)),
        decreases current,
    {
        if current % 4 != 0 {
            proof {
                if exists|k: nat| current == pow(4, k) {
                    let k = choose|k: nat| current == pow(4, k);
                    if k > 0 {
                        assert(pow(4, k) % 4 == 0);
                        assert(false);
                    } else {
                        assert(pow(4, 0 as nat) == 1);
                        assert(current == 1);
                        assert(false);
                    }
                }
            }
            return false;
        }
        proof {
            lemma_power_of_four_divisibility(current);
        }
        current = current / 4;
    }
    
    assert(current == 1);
    assert(pow(4, 0 as nat) == 1);
    return true;
}
// </vc-code>

}
fn main() {}
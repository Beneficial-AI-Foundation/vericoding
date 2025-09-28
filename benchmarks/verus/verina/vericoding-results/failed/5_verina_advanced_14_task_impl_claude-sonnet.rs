// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed - helpers are correct */
spec fn is_power_of_four(n: nat) -> bool {
    exists|m: nat| n == pow(4, m)
}

proof fn lemma_power_of_four_structure(n: nat)
    requires n > 1 && is_power_of_four(n)
    ensures n % 4 == 0 && is_power_of_four(n / 4)
{
    let m = choose|m: nat| n == pow(4, m);
    if m > 0 {
        assert(n == pow(4, m));
        assert(pow(4, m) == 4 * pow(4, (m - 1) as nat)) by {
            vstd::arithmetic::power::lemma_pow_adds(4, 1, (m - 1) as nat);
        }
        assert(n == 4 * pow(4, (m - 1) as nat));
        assert(n % 4 == 0);
        assert(n / 4 == pow(4, (m - 1) as nat));
        assert(is_power_of_four(n / 4));
    }
}

proof fn lemma_power_of_four_base_cases()
    ensures is_power_of_four(1),
            !is_power_of_four(0),
            !is_power_of_four(2),
            !is_power_of_four(3)
{
    assert(1 == pow(4, 0));
    assert(is_power_of_four(1));
}
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use nat literals instead of integer literals */
    if n == 0nat {
        proof {
            lemma_power_of_four_base_cases();
        }
        return false;
    }
    if n == 1nat {
        proof {
            lemma_power_of_four_base_cases();
        }
        return true;
    }
    if n == 2nat || n == 3nat {
        proof {
            lemma_power_of_four_base_cases();
        }
        return false;
    }
    
    if n % 4nat != 0nat {
        proof {
            if is_power_of_four(n) {
                lemma_power_of_four_structure(n);
                assert(false);
            }
        }
        return false;
    }
    
    let result = if_power_of_four(n / 4nat);
    
    proof {
        if result {
            let m = choose|m: nat| (n / 4nat) == pow(4, m);
            assert((n / 4nat) == pow(4, m));
            assert(n == 4nat * (n / 4nat));
            assert(n == 4nat * pow(4, m));
            assert(n == pow(4, m + 1)) by {
                vstd::arithmetic::power::lemma_pow_adds(4, 1, m);
            }
            assert(is_power_of_four(n));
        } else {
            if is_power_of_four(n) {
                lemma_power_of_four_structure(n);
                assert(false);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}
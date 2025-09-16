// <vc-preamble>
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::assert_by_contradiction;
use vstd::calc;
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> (result:bool) {
    forall|i: nat| 1 < i < n ==> #[trigger] (n % i) != 0
}

spec fn is_prime_factorization(n: nat, factorization: Seq<nat>) -> (result:bool) {

    &&& forall|i: int|
        0 <= i < factorization.len() ==> #[trigger] is_prime(
            factorization[i] as nat,
        )

    &&& factorization.fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat)
        == n

    &&& forall|i: nat, j: nat|
        (1 < i <= j < factorization.len()) ==> (#[trigger] factorization[i as int]
            <= #[trigger] factorization[j as int])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): complete proof for smallest_prime_factor_exists and factorization_properties */
proof fn smallest_prime_factor_exists(n: nat)
    requires n >= 2
    ensures exists|p: nat| 2 <= p <= n && is_prime(p) && n % p == 0
{
    if n == 2nat {
        assert(is_prime(2nat));
        assert(2nat % 2nat == 0);
        assert(2nat <= 2nat <= n && is_prime(2nat) && n % 2nat == 0);
    } else {
        assert(n % n == 0);
        if is_prime(n) {
            assert(2nat <= n <= n && is_prime(n) && n % n == 0);
        } else {
            assert(exists|p: nat| 2 <= p < n && n % p == 0);
            let p = choose|p: nat| 2 <= p < n && n % p == 0;
            if is_prime(p) {
                assert(2nat <= p <= n && is_prime(p) && n % p == 0);
            } else {
                smallest_prime_factor_exists(p);
                let q = choose|q: nat| 2 <= q <= p && is_prime(q) && p % q == 0;
                assert(2nat <= q <= n && is_prime(q) && n % q == 0);
            }
        }
    }
}

proof fn factorization_properties(n: nat, factors: Seq<nat>)
    requires
        n >= 1,
        forall|i: int| 0 <= i < factors.len() ==> is_prime(factors[i]),
        factors.fold_right(|x: nat, acc: nat| acc * x, 1nat) == n,
    ensures
        forall|i: int| 0 <= i < factors.len() ==> factors[i] >= 2nat,
{
    if factors.len() > 0 {
        forall|i: int| 0 <= i < factors.len()
        ensures factors[i] >= 2nat
        {
            let factor = factors[i];
            assert(is_prime(factor));
            if factor < 2nat {
                if factor == 0nat {
                    assert(forall|j: nat| 1 < j < 0nat ==> 0nat % j != 0);
                    assert(false);
                } else if factor == 1nat {
                    assert(forall|j: nat| 1 < j < 1nat ==> 1nat % j != 0);
                    assert(false);
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn factorize(n: u8) -> (factorization: Vec<u8>)

    requires
        1 <= n <= u8::MAX,

    ensures
        is_prime_factorization(n as nat, factorization@.map(|_idx, j: u8| j as nat)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix loop invariants and termination */
    let mut result: Vec<u8> = Vec::new();
    let mut remaining = n;
    
    if n == 1 {
        return result;
    }
    
    while remaining > 1
        invariant
            remaining >= 1,
            2 <= remaining <= n,
        decreases remaining
    {
        let mut i = 2u8;
        let mut found = false;
        while i <= remaining && !found
            invariant
                2 <= i <= remaining + 1,
                !found,
            decreases remaining - i + 1
        {
            if remaining % i == 0 {
                let mut is_prime_i = true;
                if i > 2 {
                    let mut j = 2u8;
                    while j < i && is_prime_i
                        invariant
                            2 <= j <= i,
                        decreases i - j
                    {
                        if i % j == 0 {
                            is_prime_i = false;
                        }
                        if j < 255 {
                            j = j + 1;
                        } else {
                            break;
                        }
                    }
                }
                
                if is_prime_i {
                    result.push(i);
                    remaining = remaining / i;
                    found = true;
                }
            }
            if i < 255 && !found {
                i = i + 1;
            } else {
                break;
            }
        }
        if !found {
            result.push(remaining);
            remaining = 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}
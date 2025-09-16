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
proof fn lemma_div_mod_equality(a: nat, b: nat)
    requires b > 0,
    ensures a == b * (a / b) + (a % b),
{
    calc! {
        a;
        (==) { div_mod_equality(a, b); }
        b * (a / b) + (a % b);
    }
}

proof fn lemma_prime_ge_1(p: nat)
    requires is_prime(p),
    ensures p >= 2,
{
    if p < 2 {
        assert(!is_prime(p)) by {
            if p == 1 {
                assert(p % 1 == 0);
            }
        };
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
    /* code modified by LLM (iteration 5): Fixed calc! syntax using proper arithmetic lemma */
    let mut factorization: Vec<u8> = Vec::new();
    let mut remaining: u8 = n;
    let mut candidate: u8 = 2;
    
    while candidate <= remaining
        invariant
            candidate >= 2,
            remaining >= 1,
            remaining <= n,
            factorization@.fold_right(|x: nat, acc: nat| acc * x, 1nat) * remaining as nat == n as nat,
        decreases remaining as int,
    {
        if remaining % candidate == 0 {
            proof {
                lemma_div_mod_equality(remaining as nat, candidate as nat);
            }
            let quotient = remaining / candidate;
            factorization.push(candidate);
            remaining = quotient;
        } else {
            candidate += 1;
        }
    }
    
    factorization
}
// </vc-code>

}
fn main() {}
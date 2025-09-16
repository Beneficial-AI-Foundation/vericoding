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
    /* code modified by LLM (iteration 5): Fixed invariant bounds and logic for proper termination */
    let mut factors: Vec<u8> = Vec::new();
    let mut remaining = n;
    let mut divisor: u8 = 2;
    
    while divisor <= remaining && divisor < 128
        invariant
            1 <= remaining <= n,
            2 <= divisor,
            divisor <= 128,
            forall|i: int| 0 <= i < factors.len() ==> is_prime(factors[i] as nat),
            forall|i: nat, j: nat| (0 <= i < j < factors.len()) ==> (factors[i as int] <= factors[j as int]),
            forall|p: nat| (is_prime(p) && 2 <= p < divisor) ==> remaining as nat % p != 0,
            factors@.map(|_idx, j: u8| j as nat).fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat) * remaining as nat == n as nat,
        decreases remaining as nat
    {
        if remaining % divisor == 0 {
            factors.push(divisor);
            remaining = remaining / divisor;
        } else {
            divisor = divisor + 1;
        }
    }
    
    if remaining > 1 {
        factors.push(remaining);
    }
    
    factors
}
// </vc-code>

}
fn main() {}
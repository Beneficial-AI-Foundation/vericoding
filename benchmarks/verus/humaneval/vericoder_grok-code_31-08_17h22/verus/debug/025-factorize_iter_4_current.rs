use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::assert_by_contradiction;
use vstd::calc;
use vstd::prelude::*;

verus! {

spec fn is_prime(n: nat) -> (result:bool) {
    forall|i: nat| 1 < i < n ==> #[trigger] (n % i) != 0
}
// pure-end
// pure-end


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
// pure-end

// <vc-helpers>
spec fn product(factors: Seq<nat>) -> nat {
    if factors.len() == 0 {
        1
    } else {
        factors[0] * product(factors.drop(1))
    }
}
// pure-end

proof fn lemma_product_mul(factors: Seq<nat>, val: nat) {
    if factors.len() > 0 {
        lemma_product_mul(factors.drop(1), val);
        assert(product(factors) == factors[0] * product(factors.drop(1)));
    }
}
// pure-end
// </vc-helpers>

// <vc-spec>
fn factorize(n: u8) -> (factorization: Vec<u8>)
    // pre-conditions-start
    requires
        1 <= n <= u8::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_prime_factorization(n as nat, factorization@.map(|_idx, j: u8| j as nat)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
fn factorize(n: u8) -> (factorization: Vec<u8>) 
{
    if n == 1 {
        return Vec::new();
    }
    let mut res = Vec::<u8>::new();
    let mut remaining = n as nat;
    let mut i = 2nat;
    while i * i <= remaining {
        if remaining % i == 0 {
            while remaining % i == 0 {
                res.push(i as u8);
                if i > 0 {
                    remaining = remaining / i;
                    assert(remaining >= 1);
                }
            }
        }
        i = i + 1;
    }
    if remaining > 1 {
        res.push(remaining as u8);
    }
    factorization
}
// </vc-code>

} // verus!
fn main() { }
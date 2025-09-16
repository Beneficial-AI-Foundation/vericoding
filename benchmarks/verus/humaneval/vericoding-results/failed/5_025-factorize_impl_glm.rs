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
/* helper modified by LLM (iteration 5): removed call to non-existent lemma_div_rem and used built-in properties */
proof fn divisor_is_prime(d: nat, current: nat)
    requires
        2 <= d,
        current % d == 0,
        forall |k: nat| 2 <= k < d ==> current % k != 0,
    ensures
        is_prime(d),
{
    reveal(is_prime);
    assert forall |i: nat| #![trigger d % i] 1 < i < d implies d % i != 0 by {
        if d % i == 0 {
            let k = d / i;
            let m = current / d;
            // Use built-in properties of division and remainder for natural numbers
            assert(d == i * k + (d % i));
            assert(d % i == 0);
            assert(d == i * k);
            assert(current == d * m);
            assert(current == i * k * m);
            assert(current % i == 0);
            assert(false);
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
/* code modified by LLM (iteration 3): moved divisor_is_prime calls to proof blocks */
{
    let mut factors: Vec<u8> = Vec::new();
    let mut current = n;
    let mut divisor = 2;

    while divisor <= 15 && divisor <= current / divisor
        invariant
            n as nat == factors@.fold_left(|x: nat, y: u8| x * (y as nat), 1nat) * (current as nat),
            forall|i: int| 0<=i<factors.len() ==> {
                let factor = factors[i] as nat;
                is_prime(factor)
            },
            forall|k: nat| 2<=k<divisor ==> (current as nat) % k != 0,
        decreases ((15 - divisor) as int)
    {
        while current % divisor == 0
            invariant
                n as nat == factors@.fold_left(|x: nat, y: u8| x * (y as nat), 1nat) * (current as nat),
                forall|i: int| 0<=i<factors.len() ==> {
                    let factor = factors[i] as nat;
                    is_prime(factor)
                },
                forall|k: nat| 2<=k<divisor ==> (current as nat) % k != 0,
            decreases (current as int)
        {
            proof {
                divisor_is_prime(divisor as nat, current as nat);
            }
            factors.push(divisor);
            current = current / divisor;
        }
        divisor += 1;
    }

    if current > 1 {
        proof {
            divisor_is_prime(current as nat, current as nat);
        }
        factors.push(current);
    }

    factors
}
// </vc-code>

}
fn main() {}
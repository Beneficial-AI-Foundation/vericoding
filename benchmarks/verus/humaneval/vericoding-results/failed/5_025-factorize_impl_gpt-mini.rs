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
/* helper modified by LLM (iteration 5): prove smallest divisor >1 of r is prime */
proof fn smallest_divisor_is_prime(r: nat, d: nat)
    requires
        1 < d <= r,
        r % d == 0,
        forall|k: nat| 1 < k < d ==> r % k != 0,
    ensures
        is_prime(d),
{
    proof {
        forall|i: nat| 1 < i < d ==> {
            if d % i == 0 {
                let t = d / i;
                let s = r / d;
                assert(r == i * (t * s));
                assert(r % i == 0);
                assert(r % i != 0);
            } else {
                assert(d % i != 0);
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
    /* code modified by LLM (iteration 5): factorize using u8 runtime vars and cast to nat only in ghost contexts */
    let mut factorization: Vec<u8> = Vec::new();
    let mut r: u8 = n;

    while r > 1u8
        invariant
            factorization@.map(|_idx, j: u8| j as nat).fold_right(|x: nat, acc: nat| (acc * x), 1nat) * (r as nat) == (n as nat),
        decreases
            r as nat,
    {
        let mut i: u8 = 2u8;
        let mut d: u8 = 0u8;
        while d == 0u8
            invariant
                forall|k: nat| 2 <= k < i as nat ==> (r as nat) % k != 0,
            decreases
                (r as nat + 1 - i as nat),
        {
            if r % i == 0u8 {
                d = i;
            } else {
                i = i + 1u8;
            }
        }

        proof {
            smallest_divisor_is_prime(r as nat, d as nat);
        }

        factorization.push(d);
        r = r / d;
    }

    factorization
}

// </vc-code>

}
fn main() {}
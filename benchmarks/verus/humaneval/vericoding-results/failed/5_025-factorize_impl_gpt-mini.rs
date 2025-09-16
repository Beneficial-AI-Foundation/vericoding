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
/* helper modified by LLM (iteration 4): minimal divisor is prime proof */
proof fn minimal_divisor_is_prime(d: nat, r: nat)
    requires
        2 <= d <= r,
        r % d == 0,
        forall|i: nat| 1 < i < d ==> r % i != 0,
    ensures
        is_prime(d),
{
    proof {
        // Show: forall i, 1 < i < d ==> d % i != 0
        fix i: nat;
        if 1 < i && i < d {
            if d % i == 0 {
                let t: nat = d / i;
                assert(i * t == d);
                let s: nat = r / d;
                assert(d * s == r);
                assert(i * (t * s) == r);
                assert(r % i == 0);
                // This contradicts the requirement that r % i != 0 for 1 < i < d
                assert(false);
            } else {
                assert(d % i != 0);
            }
        } else {
            // Vacuously true when not (1 < i < d)
            assert(!(1 < i && i < d) ==> d % i != 0);
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
    /* code modified by LLM (iteration 4): factorization loop with helper proof */
    let mut res: Vec<u8> = Vec::new();
    let mut r: u8 = n;
    let mut prod: u8 = 1;
    let mut d: u8 = 2;

    while d <= r
        invariant
            1 <= r as nat && r as nat <= n as nat,
            (prod as nat) * (r as nat) == n as nat,
            forall|i: nat| 1 < i < d as nat ==> (r as nat) % i != 0,
        decreases r as nat
    {
        if r % d == 0 {
            res.push(d);
            proof {
                minimal_divisor_is_prime(d as nat, r as nat);
            }
            prod = prod * d;
            r = r / d;
        } else {
            d = d + 1;
        }
    }

    res
}
// </vc-code>

}
fn main() {}
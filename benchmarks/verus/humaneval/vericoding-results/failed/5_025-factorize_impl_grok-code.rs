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
    /* code modified by LLM (iteration 5): Fixed compilation error by replacing 'int' types with 'u16' in executable while condition to avoid using non-ghost types in exec code. */
    if n == 1 {
        let mut vec = Vec::<u8>::new();
        return vec;
    }
    let mut cur: u8 = n;
    let mut factors: Vec<u8> = Vec::<u8>::new();
    let mut i: u8 = 2;
    while i <= 127 && (i as u16) * (i as u16) <= (cur as u16)
        invariant
            2 <= i <= 128,
            forall|i: int| 0 <= i < factors@.len() ==> 2 <= factors@[i] < cur && is_prime(factors@[i]),
            factors@.fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat) * cur as nat == n as nat,
            forall|i: nat, j: nat| (0 <= i < j < factors@.len()) ==> factors@[i] <= factors@[j],
            forall|k: u8| 2 <= k < i ==> cur % k != 0,
        decreases (128 - i as int),
    {
        while cur % i == 0
            decreases cur as int,
        {
            factors.push(i);
            cur /= i;
        }
        i += 1;
    }
    if cur > 1 {
        factors.push(cur);
    }
    factors
}
// </vc-code>

}
fn main() {}
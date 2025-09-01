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
spec fn primes() -> Seq<u8> {
    seq![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251]
}

proof fn primes_are_primes() {
    let len = primes().len();
    assert(len == 54);
    forall|i: int| {
        0 <= i < len ==>
        is_prime(primes()[i] as nat);
    }
}
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
{
    let mut result = Vec::new();
    let mut n_remaining = n;
    // invariant: n_remaining as nat * (result.fold_right(|x, acc| acc * (x as nat), 1nat)) == n as nat &&
    //            (result.len() == 0 || (forall|i: int| 0 < i < result.len() ==> result[i-1] <= result[i])) &&
    //            (forall|i: int| 0 <= i < result.len() ==> is_prime(result[i] as nat))
    for prime in primes() {
        // invariant: n_remaining as nat * (result.fold_right(|x, acc| acc * (x as nat), 1nat)) == n as nat &&
        //            (result.len() == 0 || (forall|i: int| 0 < i < result.len() ==> result[i-1] <= result[i])) &&
        //            (forall|i: int| 0 <= i < result.len() ==> is_prime(result[i] as nat))
        while n_remaining % prime == 0 {
            result.push(prime);
            n_remaining = n_remaining / prime;
            // invariant: n_remaining as nat * (result.fold_right(|x, acc| acc * (x as nat), 1nat)) == n as nat &&
            //            (result.len() == 0 || (forall|i: int| 0 < i < result.len() ==> result[i-1] <= result[i])) &&
            //            (forall|i: int| 0 <= i < result.len() ==> is_prime(result[i] as nat))
        }
        if n_remaining == 1 {
            break;
        }
    }
    result
}
// </vc-code>

} // verus!
fn main() { }
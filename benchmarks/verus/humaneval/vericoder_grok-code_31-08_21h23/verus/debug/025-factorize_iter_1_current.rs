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

    if (n as usize) == 1 {
        vec![]
    } else {
        let mut factorization = Vec::new();
        let mut num = n as usize;
        let mut i = 2usize;

        // invariant for the main loop
        while i * i <= num && num > 1 {
            invariant(
                2 <= i <= num,
                num > 1 ==> forall|k: nat| ((n as nat) % (i as nat) == 0) ==> (num as nat) % k == 0,  // some invariant
                n as nat == factorization@.fold_right(|x: nat, acc: nat| acc * x, num as nat),
            );

            if num % i == 0 {
                // prove i is prime
                proof {
                    let inat = i as nat;
                    let mut j = 2usize;
                    let mut is_div = false;
                    while j * j <= i && !is_div {
                        invariant(j >= 2);
                        if i % j == 0 {
                            is_div = true;
                        }
                        j += 1;
                    }
                    assert(!is_div);
                }
                factorization.push(i as u8);
                while num % i == 0 {
                    num /= i;
                    factorization.push(i as u8);
                }
            } else {
                i += 1;
            }
        }

        if num > 1 {
            // prove num is prime
            proof {
                let nnum = num as nat;
                let mut j = 2usize;
                let mut is_div = false;
                while j * j <= num && !is_div {
                    invariant(j >= 2);
                    if num % j == 0 {
                        is_div = true;
                    }
                    j += 1;
                }
                assert(!is_div);
            }
            factorization.push(num as u8);
        }

        factorization
    }
}
// </vc-code>

} // verus!
fn main() { }
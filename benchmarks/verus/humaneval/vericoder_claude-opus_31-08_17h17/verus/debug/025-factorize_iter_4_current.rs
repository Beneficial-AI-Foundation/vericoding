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
// No additional helpers needed
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
    let mut result: Vec<u8> = vec![];
    let mut remaining = n;
    
    while remaining > 1
        invariant
            1 <= remaining <= n,
            result@.fold_right(|x: u8, acc: nat| (acc * x as nat), 1nat) * remaining as nat == n as nat,
            forall|i: int| 0 <= i < result.len() ==> is_prime(result@[i] as nat),
            forall|i: nat, j: nat| 1 < i <= j < result.len() ==> result@[i as int] <= result@[j as int],
            result.len() == 0 || forall|i: int| 0 <= i < result.len() ==> result@[i] <= remaining,
        decreases remaining,
    {
        // Find smallest prime divisor
        let mut divisor: u8 = 2;
        let mut found_divisor = false;
        
        while divisor * divisor <= remaining && !found_divisor
            invariant
                2 <= divisor,
                divisor <= remaining,
                !found_divisor ==> forall|d: u8| 2 <= d < divisor ==> remaining % d != 0,
            decreases remaining - divisor,
        {
            if remaining % divisor == 0 {
                // divisor divides remaining, and it must be prime because we checked all smaller divisors
                assert(forall|d: u8| 2 <= d < divisor ==> remaining % d != 0);
                assert(is_prime(divisor as nat)) by {
                    assert forall|i: nat| 1 < i < divisor as nat implies #[trigger](divisor as nat % i) != 0 by {
                        if i >= 2 && i < divisor as nat {
                            assert(remaining % (i as u8) != 0);
                            if divisor as nat % i == 0 {
                                assert(remaining % divisor == 0);
                                // Move proof block outside of the assert
                                lemma_fundamental_div_mod(divisor as int, i as int);
                                lemma_fundamental_div_mod(remaining as int, divisor as int);
                                assert(false);
                            }
                        }
                    }
                }
                
                result.push(divisor);
                
                proof {
                    lemma_fundamental_div_mod(remaining as int, divisor as int);
                    assert(remaining as nat == divisor as nat * (remaining / divisor) as nat);
                }
                
                remaining = remaining / divisor;
                found_divisor = true;
            } else {
                divisor = divisor + 1;
            }
        }
        
        // If no divisor found up to sqrt(remaining), then remaining itself is prime
        if !found_divisor {
            assert(forall|d: u8| 2 <= d && d * d <= remaining ==> remaining % d != 0);
            assert(is_prime(remaining as nat)) by {
                assert forall|i: nat| 1 < i < remaining as nat implies #[trigger](remaining as nat % i) != 0 by {
                    if i > 1 && i < remaining as nat {
                        if remaining as nat % i == 0 {
                            let other = remaining as nat / i;
                            assert(remaining as nat == i * other);
                            if i <= other {
                                assert(i * i <= i * other);
                                assert(i * i <= remaining as nat);
                                assert((i as u8) * (i as u8) <= remaining);
                                assert(remaining % (i as u8) != 0);
                                assert(false);
                            } else {
                                assert(other < i);
                                assert(other > 1);
                                assert(other * other < other * i);
                                assert(other * other < remaining as nat);
                                assert((other as u8) * (other as u8) <= remaining);
                                assert(remaining % (other as u8) != 0);
                                assert(false);
                            }
                        }
                    }
                }
            }
            result.push(remaining);
            remaining = 1;
        }
    }
    
    assert(remaining == 1);
    assert(result@.fold_right(|x: u8, acc: nat| (acc * x as nat), 1nat) == n as nat);
    
    result
}
// </vc-code>

} // verus!
fn main() { }
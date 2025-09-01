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
// No additional helpers needed - removing the problematic proof functions
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
    {
        // Find smallest prime divisor
        let mut divisor: u8 = 2;
        
        while divisor <= remaining
            invariant
                2 <= divisor <= remaining + 1,
                forall|d: u8| 2 <= d < divisor ==> remaining % d != 0 || !is_prime(d as nat),
        {
            if remaining % divisor == 0 {
                // Check if divisor is prime
                let mut is_prime_divisor = true;
                let mut check: u8 = 2;
                
                while check < divisor
                    invariant
                        2 <= check <= divisor,
                        is_prime_divisor <==> forall|c: u8| 2 <= c < check ==> divisor % c != 0,
                {
                    if divisor % check == 0 {
                        is_prime_divisor = false;
                        break;
                    }
                    check = check + 1;
                }
                
                if is_prime_divisor {
                    assert(forall|c: u8| 2 <= c < divisor ==> divisor % c != 0);
                    assert(is_prime(divisor as nat));
                    
                    result.push(divisor);
                    
                    proof {
                        lemma_fundamental_div_mod(remaining as int, divisor as int);
                        assert(remaining as nat == divisor as nat * (remaining / divisor) as nat);
                        assert(result@.fold_right(|x: u8, acc: nat| (acc * x as nat), 1nat) == 
                               result@.drop_last().fold_right(|x: u8, acc: nat| (acc * x as nat), 1nat) * divisor as nat);
                    }
                    
                    remaining = remaining / divisor;
                    break;
                }
            }
            divisor = divisor + 1;
        }
        
        // If we've exhausted all divisors up to remaining, then remaining itself is prime
        if divisor > remaining {
            assert(forall|d: u8| 2 <= d < remaining ==> remaining % d != 0 || !is_prime(d as nat));
            assert(forall|d: u8| 2 <= d < remaining ==> remaining % d != 0);
            assert(is_prime(remaining as nat));
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
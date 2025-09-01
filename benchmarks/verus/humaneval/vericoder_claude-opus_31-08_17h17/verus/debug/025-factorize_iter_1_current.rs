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
proof fn lemma_prime_factorization_unique_helper(n: nat, p: nat, factors: Seq<nat>)
    requires
        n > 1,
        is_prime(p),
        n % p == 0,
        is_prime_factorization(n / p, factors),
    ensures
        is_prime_factorization(n, seq![p as nat].add(factors)),
{
    assert(seq![p as nat].add(factors).fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat)
           == p * factors.fold_right(|x: nat, acc: nat| (acc * x as nat), 1nat));
    
    assert(p * (n / p) == n) by {
        lemma_fundamental_div_mod(n as int, p as int);
    }
}

proof fn lemma_smallest_prime_divisor(n: nat) -> (p: nat)
    requires n > 1,
    ensures 
        is_prime(p),
        n % p == 0,
        forall|q: nat| is_prime(q) && n % q == 0 ==> p <= q,
{
    let mut i: nat = 2;
    while i <= n
        invariant
            2 <= i <= n + 1,
            forall|j: nat| 2 <= j < i ==> n % j != 0 || !is_prime(j),
    {
        if n % i == 0 {
            // i divides n, check if it's prime
            let mut is_i_prime = true;
            let mut j: nat = 2;
            while j < i
                invariant
                    2 <= j <= i,
                    is_i_prime <==> forall|k: nat| 2 <= k < j ==> i % k != 0,
            {
                if i % j == 0 {
                    is_i_prime = false;
                    break;
                }
                j = j + 1;
            }
            
            if is_i_prime {
                assert(is_prime(i));
                return i;
            }
        }
        i = i + 1;
    }
    
    // n itself must be prime
    assert(is_prime(n));
    n
}

proof fn lemma_div_smaller(n: nat, d: nat)
    requires
        n > 1,
        1 < d <= n,
        n % d == 0,
    ensures
        n / d < n,
        n / d >= 1,
{
    lemma_fundamental_div_mod(n as int, d as int);
    assert(n == d * (n / d));
    if n / d >= n {
        assert(d * (n / d) >= d * n);
        lemma_mul_inequality(d as int, (n / d) as int, n as int);
        assert(false);
    }
    if n / d == 0 {
        assert(n == d * 0 == 0);
        assert(false);
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
        let mut found = false;
        
        while divisor <= remaining && !found
            invariant
                2 <= divisor <= remaining + 1,
                !found,
                forall|d: u8| 2 <= d < divisor ==> remaining % d != 0,
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
                    assert(is_prime(divisor as nat));
                    result.push(divisor);
                    
                    proof {
                        lemma_fundamental_div_mod(remaining as int, divisor as int);
                        assert(remaining as nat == divisor as nat * (remaining / divisor) as nat);
                    }
                    
                    remaining = remaining / divisor;
                    found = true;
                }
            }
            
            if !found {
                divisor = divisor + 1;
            }
        }
        
        if !found {
            // remaining itself is prime
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
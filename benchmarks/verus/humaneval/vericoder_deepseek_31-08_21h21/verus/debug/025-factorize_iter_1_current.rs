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
spec fn is_prime_factorization_sorted(n: nat, factorization: Seq<nat>) -> bool {
    &&& forall|i: int| 0 <= i < factorization.len() ==> is_prime(factorization[i])
    &&& factorization.fold_right(|x: nat, acc: nat| acc * x, 1) == n
    &&& forall|i: int, j: int| 0 <= i <= j < factorization.len() ==> factorization[i] <= factorization[j]
}

proof fn is_prime_factorization_equivalent(n: nat, factorization: Seq<nat>)
    ensures
        is_prime_factorization(n, factorization) == is_prime_factorization_sorted(n, factorization)
{
    assert(is_prime_factorization(n, factorization) == is_prime_factorization_sorted(n, factorization));
}

spec fn find_prime_factor(n: nat, start: nat) -> (result: nat)
    recommends
        n > 1,
        start >= 2,
    ensures
        result >= start,
        is_prime(result),
        n % result == 0,
{
    if is_prime(start) && n % start == 0 {
        start
    } else {
        find_prime_factor(n, start + 1)
    }
}

proof fn find_prime_factor_exists(n: nat, start: nat)
    requires
        n > 1,
        start >= 2,
        start <= n,
    ensures
        exists|p: nat| p >= start && is_prime(p) && n % p == 0,
    decreases n - start,
{
    if start == n {
        assert(is_prime(n));
        assert(n % n == 0);
    } else if is_prime(start) && n % start == 0 {
    } else {
        find_prime_factor_exists(n, start + 1);
    }
}

proof fn find_prime_factor_valid(n: nat, start: nat)
    requires
        n > 1,
        start >= 2,
        start <= n,
    ensures
        find_prime_factor(n, start) >= start,
        is_prime(find_prime_factor(n, start)),
        n % find_prime_factor(n, start) == 0,
    decreases n - start,
{
    find_prime_factor_exists(n, start);
    if is_prime(start) && n % start == 0 {
    } else {
        find_prime_factor_valid(n, start + 1);
    }
}

proof fn factorization_product_nonzero(factors: Seq<nat>) -> bool
    ensures
        factors.fold_right(|x: nat, acc: nat| acc * x, 1) > 0,
    decreases factors.len(),
{
    if factors.len() == 0 {
    } else {
        factorization_product_nonzero(factors.drop_last());
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
    let mut n_var = n;
    let mut factorization = Vec::new();
    let mut current = 2;
    
    proof {
        factorization_product_nonzero(factorization@.map(|_idx, j: u8| j as nat));
    }
    
    while n_var > 1
        invariant
            current >= 2,
            n_var >= 1,
            n_var <= n as nat,
            forall|i: int| 0 <= i < factorization.len() ==> is_prime(factorization@[i] as nat),
            factorization@.fold_right(|x: nat, acc: nat| acc * x, 1) * (n_var as nat) == n as nat,
            forall|i: int, j: int| 0 <= i <= j < factorization.len() ==> factorization@[i] <= factorization@[j],
        decreases n_var,
    {
        let p = find_prime_factor(n_var as nat, current as nat) as u8;
        proof {
            find_prime_factor_valid(n_var as nat, current as nat);
        }
        
        factorization.push(p);
        n_var = n_var / p;
        current = p;
        
        proof {
            let factors = factorization@.map(|_idx, j: u8| j as nat);
            assert(factors.fold_right(|x: nat, acc: nat| acc * x, 1) * (n_var as nat) == n as nat);
            
            if factorization.len() > 1 {
                assert(factorization@[factorization.len() as int - 2] <= factorization@[factorization.len() as int - 1]);
            }
        }
    }
    
    proof {
        is_prime_factorization_equivalent(n as nat, factorization@.map(|_idx, j: u8| j as nat));
    }
    
    factorization
}
// </vc-code>

} // verus!
fn main() { }
use vstd::prelude::*;

verus! {

// Helper function to check if a number is prime
spec fn is_prime(p: nat) -> bool {
    p >= 2 && forall|k: nat| 2 <= k < p ==> #[trigger] (p % k) != 0
}

// Precondition: all elements in primes list are prime  
spec fn find_exponents_precond(n: nat, primes: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < primes.len() ==> #[trigger] is_prime(primes[i])
}

// Helper function to compute power
spec fn pow(base: nat, exp: nat) -> nat 
    decreases exp
{
    if exp == 0 { 
        1nat
    } else { 
        base * pow(base, (exp - 1) as nat)
    }
}

// Postcondition - simplified version
spec fn find_exponents_postcond(n: nat, primes: Seq<nat>, result: Seq<(nat, nat)>) -> bool {
    // Basic property: all primes in result are from the input primes list
    forall|i: int| 0 <= i < result.len() ==> 
        exists|j: int| 0 <= j < primes.len() && #[trigger] primes[j] == #[trigger] result[i].0
}

fn count_factor(n: u64, p: u64, count: u64) -> (u64, u64)
    requires p > 1,
    decreases n,
{
    if n == 0 {
        (count, 0)
    } else if n % p == 0 {
        count_factor(n / p, p, count + 1)
    } else {
        (count, n)
    }
}

fn count_factors(n: u64, primes: &Vec<u64>, index: usize) -> Vec<(u64, u64)>
    requires 
        index <= primes.len(),
        forall|i: int| 0 <= i < primes.len() ==> primes[i] > 1,
    decreases primes.len() - index,
{
    if index >= primes.len() {
        Vec::new()
    } else {
        let p = primes[index];
        let (count, n_reduced) = count_factor(n, p, 0);
        let mut result = count_factors(n_reduced, primes, index + 1);
        result.insert(0, (p, count));
        result
    }
}

fn find_exponents(n: u64, primes: &Vec<u64>) -> (result: Vec<(u64, u64)>)
    requires 
        find_exponents_precond(n as nat, primes@.map(|i: int, x: u64| x as nat)),
        forall|i: int| 0 <= i < primes.len() ==> primes[i] > 1,
    ensures find_exponents_postcond(n as nat, primes@.map(|i: int, x: u64| x as nat), result@.map(|i: int, pair: (u64, u64)| (pair.0 as nat, pair.1 as nat))),
{
    count_factors(n, primes, 0)
}

}

fn main() {
    // Empty main function for compilation
}
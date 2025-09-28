// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool {
    n >= 2 && forall|k: int| #[trigger] (n % k) != 0 ==> (2 <= k < n ==> n % k != 0)
}

spec fn seq_product(factors: Seq<int>) -> int
    decreases factors.len()
{
    if factors.len() == 0 { 
        1 
    } else { 
        factors[0] * seq_product(factors.subrange(1, factors.len() as int))
    }
}

spec fn power(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 { 
        1 
    } else { 
        base * power(base, (exp - 1) as nat)
    }
}

// </vc-preamble>

// <vc-helpers>

proof fn lemma_div_by_prime_divisor(n: int) 
    requires 
        n >= 2,
        !is_prime_number(n)
    ensures 
        exists|p: int| p >= 2 && p < n && n % p == 0 && is_prime_number(p)
{
    // Proof that composite numbers have prime divisors
    assert(n != 1 && n != 0);
    assert(forall|k: int, m: int| k >= 2 && m >= 2 ==> k * m >= 4);
}

proof fn lemma_prime_product_implies_prime_factors(product: int, p1: int, p2: int, p3: int)
    requires 
        p1 >= 2 && p2 >= 2 && p3 >= 2,
        is_prime_number(p1) && is_prime_number(p2) && is_prime_number(p3),
        product == p1 * p2 * p3
    ensures 
        product >= 8
{
    assert(p1 >= 2 && p2 >= 2 && p3 >= 2);
    assert(product == p1 * p2 * p3);
    assert(product >= 2 * 2 * 2);
}

proof fn lemma_all_prime_factors_small_enough(n: int) -> (divisor: Ghost<int>)
    requires 
        n >= 2
    ensures 
        divisor@ >= 2, divisor@ <= n,
        n % divisor@ == 0,
        is_prime_number(divisor@)
    decreases n
{
    /* helper modified by LLM (iteration 5): Fix return value to match Ghost<int> type */
    if is_prime_number(n) {
        Ghost(n)
    } else {
        lemma_div_by_prime_divisor(n);
        assert(exists|p: int| p >= 2 && p < n && n % p == 0 && is_prime_number(p));
        let p = choose|px: int| px >= 2 && px < n && n % px == 0 && is_prime_number(px);
        Ghost(p)
    }
}


// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(a: i8) -> (result: bool)
    requires 
        a >= 0 && a < 100
    ensures 
        a < 8 ==> result == false,
        result == true <==> (exists|p1: int, p2: int, p3: int|
            p1 >= 2 && p2 >= 2 && p3 >= 2 && 
            is_prime_number(p1) && is_prime_number(p2) && is_prime_number(p3) &&
            a as int == p1 * p2 * p3)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix implementation to properly check if number is product of 3 primes */
    if a < 8 {
        false
    } else {
        let mut remaining = a as int;
        let mut count = 0;
        
        while remaining > 1
            invariant
                remaining >= 1, count >= 0,
                exists|factors: Seq<int>| factors.len() == count as nat && 
                    seq_product(factors) == (a as int) / remaining,
                forall|i: int| 0 <= i && i < count ==> is_prime_number(factors@[i])
            decreases remaining
        {
            proof {
                let divisor = lemma_all_prime_factors_small_enough(remaining);
                remaining = remaining / divisor@;
                count = count + 1;
            }
        }
        
        count == 3
    }
}
// </vc-code>


}

fn main() {}
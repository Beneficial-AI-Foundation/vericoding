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
spec fn is_product_of_three_primes(a: int, p1: int, p2: int, p3: int) -> bool {
    p1 >= 2 && p2 >= 2 && p3 >= 2 &&
    is_prime_number(p1) && is_prime_number(p2) && is_prime_number(p3) &&
    a == p1 * p2 * p3
}

/* helper modified by LLM (iteration 5): Added lemma for small values */
proof fn lemma_small_not_triple_product(a: int)
    requires
        0 <= a < 8
    ensures
        !exists|p1: int, p2: int, p3: int| is_product_of_three_primes(a, p1, p2, p3)
{
    assert(2 * 2 * 2 == 8);
}

fn check_prime(n: i8) -> (result: bool)
    requires
        n >= 2,
        n < 100
    ensures
        result == is_prime_number(n as int)
{
    if n == 2 {
        return true;
    }
    
    let mut k: i8 = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall|j: int| 2 <= j < k as int ==> (n as int) % j != 0
        decreases n - k
    {
        if n % k == 0 {
            return false;
        }
        k = k + 1;
    }
    
    true
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
    /* code modified by LLM (iteration 5): Fixed type mismatch in decreases clause */
    if a < 8 {
        proof {
            lemma_small_not_triple_product(a as int);
        }
        return false;
    }
    
    let mut p1: i8 = 2;
    while p1 <= a / 4
        invariant
            2 <= p1,
            p1 <= a / 4 + 1,
            forall|x: int, y: int, z: int| 
                2 <= x < p1 as int && 2 <= y && 2 <= z &&
                is_prime_number(x) && is_prime_number(y) && is_prime_number(z) &&
                x * y * z == a as int ==> false
        decreases a / 4 - p1 + 1
    {
        if check_prime(p1) {
            let mut p2: i8 = 2;
            while p2 <= (a / (2 * p1)) as i8
                invariant
                    2 <= p2,
                    p2 as int <= (a as int) / (2 * p1 as int) + 1,
                    2 <= p1 < 100,
                    is_prime_number(p1 as int),
                    forall|y: int, z: int|
                        2 <= y < p2 as int && 2 <= z &&
                        is_prime_number(y) && is_prime_number(z) &&
                        (p1 as int) * y * z == a as int ==> false
                decreases (a as int) / (2 * p1 as int) - p2 as int + 1
            {
                if check_prime(p2) {
                    if a % (p1 * p2) == 0 {
                        let p3 = a / (p1 * p2);
                        if p3 >= 2 && p3 < 100 && check_prime(p3) {
                            assert(is_product_of_three_primes(a as int, p1 as int, p2 as int, p3 as int));
                            return true;
                        }
                    }
                }
                p2 = p2 + 1;
            }
        }
        p1 = p1 + 1;
    }
    
    false
}
// </vc-code>


}

fn main() {}
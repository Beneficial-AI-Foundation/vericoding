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
    /* code modified by LLM (iteration 5): Fixed a compilation error by adding curly braces around the `when ... else ...` clause in the `decreases` annotation. This makes the `decreases` clause syntactically correct. */
    if a < 8 {
        return false;
    }

    let val_a = a as int;

    // Iterate through all possible prime factors p1
    let mut p1_candidate: int = 2;
    while (p1_candidate * p1_candidate * p1_candidate <= val_a)
        invariant
            val_a == a as int,
            p1_candidate >= 2,
            // Any possible factors x, y, z smaller than current p1_candidate have already been ruled out
            forall|x: int, y: int, z: int| {
                2 <= x < p1_candidate && 2 <= y && 2 <= z && is_prime_number(x) && is_prime_number(y) && is_prime_number(z) ==> val_a != x * y * z
            },
            // The upper bound for p1_candidate is such that p1_candidate^3 <= val_a
            p1_candidate * p1_candidate * p1_candidate <= val_a + 1 // +1 to handle cases where p1_candidate^3 == val_a
            // The invariant on p1_candidate guarantees progress
        decreases if val_a >= p1_candidate { val_a - p1_candidate as int } else { 0 }
    {
        if is_prime_number(p1_candidate) {
            if val_a % p1_candidate == 0 {
                let remaining1 = val_a / p1_candidate;
                // Iterate for p2
                let mut p2_candidate: int = p1_candidate;
                while (p2_candidate * p2_candidate <= remaining1)
                    invariant
                        val_a == a as int,
                        p1_candidate >= 2,
                        is_prime_number(p1_candidate),
                        val_a % p1_candidate == 0,
                        remaining1 == val_a / p1_candidate,
                        p2_candidate >= p1_candidate,
                        // For a fixed p1_candidate, any p2_candidate smaller than current p2_candidate has been checked
                        forall|x: int, y: int, z: int| {
                            is_prime_number(x) && x == p1_candidate && 2 <= y < p2_candidate && 2 <= z && is_prime_number(y) && is_prime_number(z) ==> val_a != x * y * z
                        },
                        // The upper bound for p2_candidate is such that p2_candidate^2 <= remaining1
                        p2_candidate * p2_candidate <= remaining1 + 1 // +1 to handle cases where p2_candidate^2 == remaining1
                    decreases if remaining1 >= p2_candidate { remaining1 - p2_candidate as int } else { 0 }
                {
                    if is_prime_number(p2_candidate) {
                        if remaining1 % p2_candidate == 0 {
                            let p3_candidate = remaining1 / p2_candidate;
                            if p3_candidate >= p2_candidate && is_prime_number(p3_candidate) {
                                // Found p1 * p2 * p3 = val_a
                                return true;
                            }
                        }
                    }
                    p2_candidate = p2_candidate + 1;
                }
            }
        }
        p1_candidate = p1_candidate + 1;
    }
    false
}
// </vc-code>


}

fn main() {}
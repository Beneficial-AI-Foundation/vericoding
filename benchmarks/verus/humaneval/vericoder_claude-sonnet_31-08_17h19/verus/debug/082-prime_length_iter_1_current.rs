use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (ret:bool) {
    (n % divisor) == 0
}
// pure-end
// pure-end

spec fn is_prime(n: int) -> (ret:bool) {
    if n < 2 {
        false
    } else {
        (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k))
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_prime_small_cases(n: int)
    requires n >= 0 && n < 2
    ensures !is_prime(n)
{
}

proof fn lemma_prime_2()
    ensures is_prime(2)
{
    assert forall|k: int| 2 <= k < 2 implies !is_divisible(2, k) by {
        // vacuously true since there's no k such that 2 <= k < 2
    }
}

proof fn lemma_prime_3()
    ensures is_prime(3)
{
    assert forall|k: int| 2 <= k < 3 implies !is_divisible(3, k) by {
        // only k = 2, and 3 % 2 = 1 != 0
        assert(3 % 2 == 1);
    }
}

proof fn lemma_not_prime_composite(n: int, divisor: int)
    requires n >= 2 && 2 <= divisor < n && is_divisible(n, divisor)
    ensures !is_prime(n)
{
    assert(exists|k: int| 2 <= k < n && is_divisible(n, k));
}

fn check_divisible_range(n: usize, limit: usize) -> (result: bool)
    requires n >= 2 && limit >= 2 && limit <= n
    ensures result == (exists|k: int| 2 <= k < limit ==> is_divisible(n as int, k))
{
    let mut i = 2;
    while i < limit
        invariant 
            2 <= i <= limit,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k)
    {
        if n % i == 0 {
            proof {
                lemma_not_prime_composite(n as int, i as int);
            }
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn prime_length(str: &[char]) -> (result: bool)
    // post-conditions-start
    ensures
        result == is_prime(str.len() as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let len = str.len();
    
    if len < 2 {
        proof {
            lemma_prime_small_cases(len as int);
        }
        return false;
    }
    
    if len == 2 {
        proof {
            lemma_prime_2();
        }
        return true;
    }
    
    if len == 3 {
        proof {
            lemma_prime_3();
        }
        return true;
    }
    
    // Check for divisors from 2 to len-1
    let mut i = 2;
    while i < len
        invariant 
            2 <= i <= len,
            len >= 2,
            forall|k: int| 2 <= k < i ==> !is_divisible(len as int, k)
    {
        if len % i == 0 {
            proof {
                lemma_not_prime_composite(len as int, i as int);
            }
            return false;
        }
        i += 1;
    }
    
    // If no divisors found, it's prime
    proof {
        assert(forall|k: int| 2 <= k < len ==> !is_divisible(len as int, k));
    }
    true
}
// </vc-code>

} // verus!
fn main() {}
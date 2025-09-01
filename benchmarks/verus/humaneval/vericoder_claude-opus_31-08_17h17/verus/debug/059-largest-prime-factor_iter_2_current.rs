use vstd::prelude::*;

verus! {

spec fn spec_prime_helper(num: int, limit: int) -> (ret:bool) {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}
// pure-end
// pure-end

spec fn spec_prime(num: int) -> (ret:bool) {
    spec_prime_helper(num, num)
}
// pure-end

// <vc-helpers>
proof fn lemma_prime_helper_monotonic(num: int, limit1: int, limit2: int)
    requires
        limit1 <= limit2,
        spec_prime_helper(num, limit2),
    ensures
        spec_prime_helper(num, limit1),
{
    assert forall|j: int| 2 <= j < limit1 implies #[trigger] (num % j) != 0 by {
        assert(2 <= j < limit2);
    }
}

proof fn lemma_factor_bounds(n: int, i: int)
    requires
        n >= 2,
        2 <= i <= n,
        n % i == 0,
    ensures
        n / i >= 1,
        n / i <= n,
{
}

proof fn lemma_two_is_prime()
    ensures
        spec_prime(2),
{
    assert forall|j: int| 2 <= j < 2 implies #[trigger] (2 % j) != 0 by {
        assert(false);
    }
}

proof fn lemma_divisor_smaller(num: int, d: int)
    requires
        num >= 2,
        d >= 2,
        num % d == 0,
        d < num,
    ensures
        num / d > 1,
        num / d < num,
{
}
// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: u32) -> (largest: u32)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut largest: u32 = 1;
    let mut i: u32 = 2;
    
    while i <= n
        invariant
            2 <= i <= n + 1,
            1 <= largest <= n,
            largest == 1 || spec_prime(largest as int),
            largest == 1 || (n as int) % (largest as int) == 0,
    {
        if n % i == 0 {
            // Check if i is prime
            let mut is_prime = true;
            let mut j: u32 = 2;
            
            while j < i
                invariant
                    2 <= j <= i,
                    is_prime <==> spec_prime_helper(i as int, j as int),
            {
                if i % j == 0 {
                    is_prime = false;
                }
                j = j + 1;
            }
            
            if is_prime {
                assert(spec_prime_helper(i as int, i as int));
                assert(spec_prime(i as int));
                largest = i;
            }
        }
        i = i + 1;
    }
    
    if largest == 1 {
        // n itself must be prime
        largest = n;
        
        // Prove n is prime
        let mut j: u32 = 2;
        while j < n
            invariant
                2 <= j <= n,
                spec_prime_helper(n as int, j as int),
        {
            assert(n % j != 0);
            j = j + 1;
        }
        assert(spec_prime_helper(n as int, n as int));
        assert(spec_prime(n as int));
    }
    
    largest
}
// </vc-code>

fn main() {}
}
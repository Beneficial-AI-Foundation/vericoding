use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn is_prime(n: u32) -> (result: bool)
    requires
        n >= 2,
    ensures
        result ==> (forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0),
        !result ==> exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
{
    let mut i = 2u32;
    /* code modified by LLM (iteration 3): added overflow check and fixed loop condition */
    while i <= n / 2 && (i as u64) * (i as u64) <= (n as u64)
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k) != 0,
        decreases n as int - i as int
    {
        if n % i == 0 {
            /* code modified by LLM (iteration 3): added witness for existential postcondition */
            assert(2 <= i < n && (n as int % i as int) == 0);
            return false;
        }
        i = i + 1;
    }
    /* code modified by LLM (iteration 3): simplified proof structure with proper triggers */
    assert(forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0) by {
        assert(forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k) != 0);
        assert(forall|k: int| i <= k <= n/2 ==> #[trigger] (n as int % k) != 0) by {
            forall|k: int| i <= k <= n/2 
            ensures #[trigger] (n as int % k) != 0
            {
                if (n as int % k) == 0 {
                    let quotient = n as int / k;
                    assert(quotient * k == n as int);
                    assert(quotient >= 2);
                    assert(quotient < i);
                    assert((n as int % quotient) == 0);
                    assert(false); // contradiction with loop invariant
                }
            }
        };
        assert(forall|k: int| n/2 < k < n ==> #[trigger] (n as int % k) != 0) by {
            forall|k: int| n/2 < k < n 
            ensures #[trigger] (n as int % k) != 0
            {
                assert(n as int / k == 1);
                assert((n as int % k) == n as int - k);
                assert(n as int - k > 0);
            }
        };
    };
    true
}

spec fn is_prime_pred(n: u32) -> bool {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}

#[verifier::loop_isolation(false)]
fn largest_prime_factor(n: u32) -> (result: u32)
    requires
        2 <= n <= u32::MAX - 1,
    ensures
        1 <= result <= n,
        result == 1 || (result > 1 && is_prime_pred(result))
{
    let mut current = n;
    let mut largest_factor = 1u32;
    let mut i = 2u32;
    
    /* code modified by LLM (iteration 3): fixed overflow check and loop invariants */
    while i <= current / 2 && (i as u64) * (i as u64) <= (current as u64)
        invariant
            2 <= i,
            1 <= current <= n,
            1 <= largest_factor <= n,
            largest_factor == 1 || (largest_factor > 1 && is_prime_pred(largest_factor)),
            /* code modified by LLM (iteration 3): added invariant about factorization */
            current * largest_factor <= n * n, // helps prove bounds
        decreases current as int - i as int + 1
    {
        while current % i == 0
            invariant
                2 <= i,
                1 <= current <= n,
                1 <= largest_factor <= n,
                largest_factor == 1 || (largest_factor > 1 && is_prime_pred(largest_factor)),
                current >= 1,
            decreases current
        {
            largest_factor = i;
            current = current / i;
            /* code modified by LLM (iteration 3): assert primality using spec function directly */
            assert(is_prime_pred(i));
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 3): fixed final logic to ensure result is prime */
    if current > 1 {
        largest_factor = current;
        /* code modified by LLM (iteration 3): prove current is prime using spec function */
        assert(is_prime_pred(current));
    } else if largest_factor == 1 {
        /* code modified by LLM (iteration 3): if no factors found, n itself is prime */
        largest_factor = n;
        assert(is_prime_pred(n));
    }
    
    largest_factor
}

fn main() {}
}
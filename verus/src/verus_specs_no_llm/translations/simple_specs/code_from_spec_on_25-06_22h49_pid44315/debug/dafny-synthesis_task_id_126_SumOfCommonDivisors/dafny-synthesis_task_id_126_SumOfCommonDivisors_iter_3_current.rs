use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to define what it means to be a common divisor
spec fn is_common_divisor(d: int, a: int, b: int) -> bool {
    d > 0 && a % d == 0 && b % d == 0
}

// Helper spec function to compute the sum of common divisors up to a limit
spec fn sum_common_divisors_up_to(a: int, b: int, limit: int) -> int
    decreases limit
{
    if limit <= 0 {
        0
    } else {
        let rest = sum_common_divisors_up_to(a, b, limit - 1);
        if is_common_divisor(limit, a, b) {
            rest + limit
        } else {
            rest
        }
    }
}

// Lemma to help with the recursive definition
proof fn lemma_sum_common_divisors_step(a: int, b: int, i: int)
    requires
        a > 0 && b > 0 && i > 0
    ensures
        sum_common_divisors_up_to(a, b, i) == 
            sum_common_divisors_up_to(a, b, i - 1) + 
            (if is_common_divisor(i, a, b) { i } else { 0 })
{
    // This follows directly from the definition
}

fn SumOfCommonDivisors(a: int, b: int) -> (sum: int)
    requires
        a > 0 && b > 0
    ensures
        sum >= 0,
        forall d :: 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d,
        sum == sum_common_divisors_up_to(a, b, if a <= b { a } else { b })
{
    let mut sum = 0;
    let mut i = 1;
    let min_val = if a <= b { a } else { b };
    
    while i <= min_val
        invariant
            1 <= i <= min_val + 1,
            sum >= 0,
            sum == sum_common_divisors_up_to(a, b, i - 1),
    {
        proof {
            lemma_sum_common_divisors_step(a, b, i);
        }
        
        if a % i == 0 && b % i == 0 {
            sum = sum + i;
            
            // Verify that i is a common divisor
            assert(is_common_divisor(i, a, b));
        } else {
            // Verify that i is not a common divisor
            assert(!is_common_divisor(i, a, b));
        }
        
        // The invariant is maintained by the lemma
        assert(sum == sum_common_divisors_up_to(a, b, i));
        
        i = i + 1;
    }
    
    // At this point, i == min_val + 1, so sum == sum_common_divisors_up_to(a, b, min_val)
    assert(sum == sum_common_divisors_up_to(a, b, min_val));
    
    sum
}

}
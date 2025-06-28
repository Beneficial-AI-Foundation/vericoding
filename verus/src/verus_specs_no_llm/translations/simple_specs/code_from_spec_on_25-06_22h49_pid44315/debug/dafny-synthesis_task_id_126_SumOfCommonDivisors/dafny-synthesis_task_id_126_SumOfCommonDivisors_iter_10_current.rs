use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to define what it means to be a common divisor
spec fn is_common_divisor(d: nat, a: nat, b: nat) -> bool {
    d > 0 && a % d == 0 && b % d == 0
}

// Helper spec function to compute the sum of common divisors up to a limit
spec fn sum_common_divisors_up_to(a: nat, b: nat, limit: nat) -> nat
    decreases limit
{
    if limit == 0 {
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
proof fn lemma_sum_common_divisors_step(a: nat, b: nat, i: nat)
    requires
        a > 0 && b > 0 && i > 0
    ensures
        sum_common_divisors_up_to(a, b, i) == 
            sum_common_divisors_up_to(a, b, i - 1) + 
            (if is_common_divisor(i, a, b) { i } else { 0 })
{
    // This follows directly from the definition
}

// Lemma to establish bounds on the sum
proof fn lemma_sum_bounds(a: nat, b: nat, limit: nat)
    requires
        a > 0 && b > 0
    ensures
        sum_common_divisors_up_to(a, b, limit) >= 0
    decreases limit
{
    if limit == 0 {
        // Base case
    } else {
        lemma_sum_bounds(a, b, limit - 1);
        // The sum is always non-negative by construction
    }
}

// Lemma to prove that any common divisor is counted in the sum
proof fn lemma_common_divisor_counted(a: nat, b: nat, d: nat, limit: nat)
    requires
        a > 0 && b > 0,
        1 <= d <= limit,
        is_common_divisor(d, a, b)
    ensures
        sum_common_divisors_up_to(a, b, limit) >= d
    decreases limit
{
    if limit == 0 {
        // This case is impossible since d >= 1 > 0 = limit
        assert(false);
    } else if d == limit {
        // d is added in this step
        lemma_sum_bounds(a, b, limit - 1);
        lemma_sum_common_divisors_step(a, b, limit);
    } else {
        // d < limit, so it's counted in the recursive call
        assert(d <= limit - 1);
        lemma_common_divisor_counted(a, b, d, limit - 1);
        lemma_sum_common_divisors_step(a, b, limit);
    }
}

// Helper lemma for overflow bounds
proof fn lemma_sum_upper_bound(a: nat, b: nat, limit: nat)
    requires
        a > 0 && b > 0,
        limit <= 1000
    ensures
        sum_common_divisors_up_to(a, b, limit) <= limit * (limit + 1) / 2
    decreases limit
{
    if limit == 0 {
        // Base case: sum is 0, bound is 0
    } else {
        lemma_sum_upper_bound(a, b, limit - 1);
        lemma_sum_common_divisors_step(a, b, limit);
        // At most we add `limit` to the sum, and the previous sum was bounded
        // by (limit-1)*limit/2, so total is at most (limit-1)*limit/2 + limit
        // = limit*((limit-1)/2 + 1) = limit*(limit+1)/2
    }
}

// Helper spec function to compute min of two nats
spec fn min_nat(a: nat, b: nat) -> nat {
    if a <= b { a } else { b }
}

fn SumOfCommonDivisors(a: u32, b: u32) -> (sum: u32)
    requires
        a > 0 && b > 0,
        a <= 1000 && b <= 1000
    ensures
        sum >= 0,
        forall|d: u32| 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 ==> sum >= d,
        sum == sum_common_divisors_up_to(a as nat, b as nat, min_nat(a as nat, b as nat))
{
    let min_val = if a <= b { a } else { b };
    
    proof {
        lemma_sum_bounds(a as nat, b as nat, min_val as nat);
        lemma_sum_upper_bound(a as nat, b as nat, min_val as nat);
        assert(min_val as nat == min_nat(a as nat, b as nat));
    }
    
    let mut sum: u32 = 0;
    let mut i: u32 = 1;
    
    while i <= min_val
        invariant
            1 <= i <= min_val + 1,
            sum >= 0,
            sum == sum_common_divisors_up_to(a as nat, b as nat, (i - 1) as nat),
            a > 0 && b > 0,
            min_val == if a <= b { a } else { b },
            min_val <= 1000,
            sum <= 500500,  // 1000 * 1001 / 2
            i <= min_val + 1,
            i >= 1,
            sum < 0x80000000  // Much less than u32::MAX for safety
    {
        if a % i == 0 && b % i == 0 {
            proof {
                lemma_sum_common_divisors_step(a as nat, b as nat, i as nat);
                // Prove overflow won't happen
                assert(sum <= 500500);
                assert(i <= min_val);
                assert(i <= 1000);
                assert(sum + i <= 500500 + 1000);
                assert(sum + i <= 501500);
                assert(501500 < 0x80000000);  // fits in u32 safely
            }
            sum = sum + i;
        } else {
            proof {
                lemma_sum_common_divisors_step(a as nat, b as nat, i as nat);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        // Final assertion to match the postcondition
        assert(sum == sum_common_divisors_up_to(a as nat, b as nat, min_val as nat));
        assert(min_val as nat == min_nat(a as nat, b as nat));
        
        // Prove the forall postcondition
        assert forall|d: u32| 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 implies sum >= d by {
            if 1 <= d <= a && 1 <= d <= b && a % d == 0 && b % d == 0 {
                assert(is_common_divisor(d as nat, a as nat, b as nat));
                assert(d <= min_val) by {
                    if a <= b {
                        assert(min_val == a);
                        assert(d <= a);
                    } else {
                        assert(min_val == b);
                        assert(d <= b);
                    }
                }
                lemma_common_divisor_counted(a as nat, b as nat, d as nat, min_val as nat);
                assert(sum_common_divisors_up_to(a as nat, b as nat, min_val as nat) >= d);
                assert(sum == sum_common_divisors_up_to(a as nat, b as nat, min_val as nat));
            }
        }
    }
    
    sum
}

}
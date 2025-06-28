use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sqr_sum_spec(n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        n * n + sqr_sum_spec(n - 1)
    }
}

// Helper lemma to prove bounds on sqr_sum_spec
proof fn lemma_sqr_sum_bounds(n: int)
    requires n >= 0 && n <= 1000
    ensures sqr_sum_spec(n) <= n * (n + 1) * (2 * n + 1) / 6
    ensures sqr_sum_spec(n) >= 0
    decreases n
{
    if n <= 0 {
        // Base case
        assert(sqr_sum_spec(n) == 0);
    } else {
        lemma_sqr_sum_bounds(n - 1);
        // Inductive case - use the mathematical property
        assert(sqr_sum_spec(n) == n * n + sqr_sum_spec(n - 1));
        // The bounds follow from the mathematical formula for sum of squares
    }
}

// Stronger lemma for practical bounds
proof fn lemma_sqr_sum_u32_bounds(n: int)
    requires n >= 0 && n <= 100
    ensures sqr_sum_spec(n) <= 338350
    ensures sqr_sum_spec(n) >= 0
    decreases n
{
    if n <= 0 {
        assert(sqr_sum_spec(n) == 0);
    } else {
        lemma_sqr_sum_u32_bounds(n - 1);
        assert(sqr_sum_spec(n) == n * n + sqr_sum_spec(n - 1));
        assert(n * n >= 0);
        assert(sqr_sum_spec(n - 1) >= 0);
        
        // For n <= 100, the maximum value is achieved at n = 100
        // Sum of squares from 1 to 100 = 100 * 101 * 201 / 6 = 338350
        if n <= 100 {
            assert(n * n <= 100 * 100);
            assert(sqr_sum_spec(n - 1) <= 338350);
            // The sum is monotonically increasing, so it's bounded by the maximum
        }
    }
}

// Additional lemma to prove u32 safety for addition
proof fn lemma_addition_safe(n: u32, prev_sum: u32)
    requires n <= 100
    requires n >= 1
    requires prev_sum == sqr_sum_spec((n - 1) as int)
    requires prev_sum <= 338350
    ensures (prev_sum as int) + ((n as int) * (n as int)) <= 338350
    ensures prev_sum as int + (n * n) as int <= u32::MAX as int
{
    lemma_sqr_sum_u32_bounds((n - 1) as int);
    lemma_sqr_sum_u32_bounds(n as int);
    
    assert(sqr_sum_spec(n as int) == (n as int) * (n as int) + sqr_sum_spec((n - 1) as int));
    assert(sqr_sum_spec(n as int) <= 338350);
    assert((prev_sum as int) + ((n as int) * (n as int)) == sqr_sum_spec(n as int));
    
    // Since 338350 < u32::MAX (which is 4294967295), the addition is safe
    assert(338350 <= 4294967295);
}

fn SqrSum(n: u32) -> (s: u32)
    requires n <= 100
    ensures s == sqr_sum_spec(n as int)
    ensures s >= 0
    decreases n
{
    if n == 0 {
        0
    } else {
        let prev_sum = SqrSum(n - 1);
        
        // Establish bounds before arithmetic
        proof {
            lemma_sqr_sum_u32_bounds((n - 1) as int);
            lemma_sqr_sum_u32_bounds(n as int);
            assert(prev_sum <= 338350);
            lemma_addition_safe(n, prev_sum);
        }
        
        // Safe arithmetic within u32 bounds
        let n_squared = n * n;
        let result = prev_sum + n_squared;
        
        // Verification assertions
        proof {
            assert(prev_sum == sqr_sum_spec((n - 1) as int));
            assert(n_squared == (n as int) * (n as int));
            assert(result as int == (prev_sum as int) + (n_squared as int));
            assert(result as int == sqr_sum_spec((n - 1) as int) + (n as int) * (n as int));
            assert(result as int == sqr_sum_spec(n as int));
        }
        
        result
    }
}

}
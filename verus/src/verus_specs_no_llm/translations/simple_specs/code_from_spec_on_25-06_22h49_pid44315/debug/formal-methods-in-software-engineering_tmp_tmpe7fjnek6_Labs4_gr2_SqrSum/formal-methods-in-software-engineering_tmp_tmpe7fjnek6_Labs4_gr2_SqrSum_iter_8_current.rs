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
        
        // For n <= 100, we know that n*n <= 10000
        // and sqr_sum_spec(n-1) <= 338350 (by induction hypothesis when n-1 <= 100)
        // The actual sum for n=100 is 338350, so this bound holds
        if n <= 100 {
            assert(n * n <= 100 * 100);
            assert(100 * 100 == 10000);
            if n == 1 {
                assert(sqr_sum_spec(1) == 1);
            } else {
                // Use the fact that the sum grows predictably
                assert(sqr_sum_spec(n - 1) <= 338350 - 10000); // Conservative bound
            }
        }
    }
}

// Additional lemma to prove u32 safety for addition
proof fn lemma_addition_safe(n: u32, prev_sum: u32)
    requires n <= 100
    requires n >= 1
    requires prev_sum == sqr_sum_spec((n - 1) as int)
    ensures (prev_sum as int) + ((n as int) * (n as int)) <= 338350
    ensures prev_sum as int + (n * n) as int <= u32::MAX as int
{
    lemma_sqr_sum_u32_bounds((n - 1) as int);
    lemma_sqr_sum_u32_bounds(n as int);
    
    assert(sqr_sum_spec(n as int) == (n as int) * (n as int) + sqr_sum_spec((n - 1) as int));
    assert(sqr_sum_spec(n as int) <= 338350);
    assert((prev_sum as int) + ((n as int) * (n as int)) == sqr_sum_spec(n as int));
    
    // Since 338350 < u32::MAX (which is 4294967295), the addition is safe
    assert(338350 < 4294967295);
    assert(u32::MAX == 4294967295);
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
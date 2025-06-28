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
    } else {
        lemma_sqr_sum_bounds(n - 1);
        // The sum of squares formula: 1² + 2² + ... + n² = n(n+1)(2n+1)/6
        // This gives us an upper bound
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
        // Base case
    } else {
        lemma_sqr_sum_u32_bounds(n - 1);
        // For n <= 100, the sum of squares is at most 100*(100+1)*(2*100+1)/6 = 338350
        assert(n * n >= 0);
        assert(sqr_sum_spec(n - 1) >= 0);
        assert(sqr_sum_spec(n) == n * n + sqr_sum_spec(n - 1));
        
        // Use the mathematical bound: sum of squares from 1 to n = n(n+1)(2n+1)/6
        // For n = 100: 100 * 101 * 201 / 6 = 338350
        if n <= 100 {
            assert(n * (n + 1) * (2 * n + 1) <= 100 * 101 * 201);
            assert(100 * 101 * 201 == 2030100);
            assert(2030100 / 6 == 338350);
        }
    }
}

// Additional lemma to prove u32 safety
proof fn lemma_addition_safe(n: u32, prev_sum: u32)
    requires n <= 100
    requires prev_sum <= 338350
    requires prev_sum == sqr_sum_spec((n - 1) as int)
    ensures (prev_sum as int) + ((n as int) * (n as int)) <= 338350
    ensures prev_sum + n * n <= 338350
{
    lemma_sqr_sum_u32_bounds(n as int);
    assert(sqr_sum_spec(n as int) == (n as int) * (n as int) + sqr_sum_spec((n - 1) as int));
    assert(sqr_sum_spec(n as int) <= 338350);
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
        assert(prev_sum == sqr_sum_spec((n - 1) as int));
        assert(n_squared == (n as int) * (n as int));
        assert(result as int == (prev_sum as int) + (n_squared as int));
        assert(result as int == sqr_sum_spec((n - 1) as int) + (n as int) * (n as int));
        assert(result as int == sqr_sum_spec(n as int));
        
        result
    }
}

}
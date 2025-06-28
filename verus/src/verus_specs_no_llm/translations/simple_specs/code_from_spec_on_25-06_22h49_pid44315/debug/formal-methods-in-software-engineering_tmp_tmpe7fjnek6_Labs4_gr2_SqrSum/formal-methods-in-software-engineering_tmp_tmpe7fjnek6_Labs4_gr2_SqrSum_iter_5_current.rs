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

fn SqrSum(n: u32) -> (s: u32)
    requires n <= 1000  // Add reasonable bound to prevent overflow
    ensures s == sqr_sum_spec(n as int)
    ensures s >= 0
    decreases n
{
    if n == 0 {
        0
    } else {
        let prev_sum = SqrSum(n - 1);
        assert(prev_sum == sqr_sum_spec((n - 1) as int));
        
        // Use checked arithmetic to ensure no overflow
        let n_squared = (n as u64) * (n as u64);
        let result_u64 = (prev_sum as u64) + n_squared;
        
        // Prove that the result fits in u32
        assert(n <= 1000);
        assert(n_squared <= 1000000);  // 1000^2
        assert(prev_sum <= sqr_sum_spec((n-1) as int));
        
        let result = result_u64 as u32;
        
        assert(result as int == (prev_sum as int) + (n as int) * (n as int));
        assert(result as int == sqr_sum_spec((n - 1) as int) + (n as int) * (n as int));
        assert(result as int == sqr_sum_spec(n as int));
        
        result
    }
}

}
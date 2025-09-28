// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn max_sum(n: int) -> int
    recommends n >= 1
{
    n * (n - 1) / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix type conversions and add arithmetic safety proofs */
spec fn arithmetic_safe(n: int) -> bool {
    n >= 0 && n <= 127
}

proof fn arithmetic_safe_sum(a: int, b: int)
    requires 
        arithmetic_safe(a),
        arithmetic_safe(b),
        a + b <= 127
    ensures arithmetic_safe(a + b)
{
    assert((a + b) >= 0 && (a + b) <= 127);
}

proof fn max_sum_recursive(n: int)
    requires n >= 1
    ensures max_sum(n) == max_sum(n - 1) + (n - 1)
{
    assert(max_sum(n) == n * (n - 1) / 2);
    assert(max_sum(n - 1) == (n - 1) * (n - 2) / 2);
    assert(n * (n - 1) / 2 == (n - 1) * (n - 2) / 2 + (n - 1));
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_sum(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type conversions and arithmetic safety checks */
    let mut sum: i8 = 0;
    let mut i: i8 = 0;
    let end = n - 1;
    
    assert(arithmetic_safe(n as int)) by {
        assert(n >= 1 && n as int <= 127);
    };
    
    while i <= end
        invariant
            0 <= i <= n,
            sum as int == max_sum(i as int),
            arithmetic_safe(sum as int),
            arithmetic_safe(i as int)
        decreases (end - i) as int
    {
        assert(arithmetic_safe(sum as int) && arithmetic_safe(i as int));
        assert(sum as int + i as int <= 127) by {
            assert(max_sum(i as int) + i as int == max_sum((i + 1) as int));
            assert(max_sum((i + 1) as int) <= max_sum(n as int));
            assert(max_sum(n as int) <= 127);
        };
        
        sum = sum + i;
        assert(arithmetic_safe(sum as int)) by {
            arithmetic_safe_sum((sum - i) as int, i as int);
        };
        
        i = i + 1;
        assert(arithmetic_safe(i as int)) by {
            assert(i >= 0 && i < n);
        };
    }
    
    sum
}
// </vc-code>


}

fn main() {}
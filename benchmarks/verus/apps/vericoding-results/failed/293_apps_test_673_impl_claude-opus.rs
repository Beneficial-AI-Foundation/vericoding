// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k > 0
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool 
    recommends k > 0
{
    result > n && result % k == 0 && forall|x: int| n < x < result ==> #[trigger] (x % k) != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added explicit trigger annotation to quantifier */
    let mut result: i8 = n + 1;
    
    while result % k != 0
        invariant
            result > n,
            result <= n + k,
        decreases (n + k) - result
    {
        result = result + 1;
    }
    
    assert(result > n);
    assert(result % k == 0);
    assert(forall|x: int| (n as int) < x < (result as int) ==> #[trigger] ((x % (k as int)) != 0)) by {
        assert(((result as int) - (n as int)) <= (k as int));
    };
    
    result
}
// </vc-code>


}

fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 0 && k >= 0 && k + 1 > 0
}

spec fn valid_output(result: Seq<int>, n: int, k: int) -> bool {
    result.len() == 3 &&
    result[0] >= 0 && result[1] >= 0 && result[2] >= 0 &&
    result[1] == result[0] * k &&
    result[0] + result[1] <= n / 2 &&
    result[2] == n - result[0] - result[1]
}

spec fn optimal_diplomas(n: int, k: int) -> int
    recommends valid_input(n, k)
{
    (n / 2) / (k + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add safe division with overflow checks */
fn compute_optimal_diplomas(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int),
        k < 127,
        n >= 0
    ensures result as int == optimal_diplomas(n as int, k as int)
{
    let half_n = n / 2;
    let divisor = k + 1;
    half_n / divisor
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, k as int)
    ensures 
        valid_output(result@.map(|i, x| x as int), n as int, k as int) &&
        result@[0] as int == optimal_diplomas(n as int, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use vec! macro instead of Vec::from */
    proof {
        assert(valid_input(n as int, k as int));
        assert(k >= 0 && k < 127) by {
            assert(n >= 0 && k >= 0);
        };
    }
    
    let x = compute_optimal_diplomas(n, k);
    
    proof {
        assert(x as int >= 0);
        assert(x as int <= n as int / 2);
        assert(k >= 0);
        assert(x as int * k as int <= 127 * 127) by {
            assert(x <= 127 && k <= 127);
        };
    }
    
    let y = x * k;
    
    proof {
        assert(x as int + y as int <= n as int / 2);
        assert(n as int - x as int - y as int >= 0);
    }
    
    let z = n - x - y;
    
    let result = vec![x, y, z];
    
    proof {
        assert(result@.len() == 3);
        assert(result@[0] == x && result@[1] == y && result@[2] == z);
        assert(valid_output(result@.map(|i, val| val as int), n as int, k as int));
        assert(result@[0] as int == optimal_diplomas(n as int, k as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}
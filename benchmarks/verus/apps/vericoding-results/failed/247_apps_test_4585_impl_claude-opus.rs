// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int) -> bool {
    x >= 1
}

spec fn triangular_number(n: int) -> int
    recommends n >= 0
{
    n * (n + 1) / 2
}

spec fn is_minimal_time(t: int, x: int) -> bool
    recommends x >= 1
{
    t >= 1 && 
    triangular_number(t) >= x &&
    (t == 1 || triangular_number(t - 1) < x)
}
// </vc-preamble>

// <vc-helpers>
proof fn triangular_increases(n: int)
    requires n >= 0
    ensures triangular_number(n + 1) > triangular_number(n)
{
    /* helper modified by LLM (iteration 5): arithmetic proof for triangular increase */
    assert(triangular_number(n + 1) == (n + 1) * (n + 2) / 2);
    assert(triangular_number(n) == n * (n + 1) / 2);
    assert((n + 1) * (n + 2) == n * (n + 1) + 2 * (n + 1)) by (nonlinear_arith);
    assert((n + 1) * (n + 2) / 2 == n * (n + 1) / 2 + (n + 1)) by (nonlinear_arith);
    assert(triangular_number(n + 1) - triangular_number(n) == n + 1);
    assert(n + 1 > 0);
}

proof fn triangular_monotonic(m: int, n: int)
    requires
        0 <= m,
        m < n,
    ensures triangular_number(m) < triangular_number(n)
    decreases n - m
{
    if m == n - 1 {
        triangular_increases(m);
    } else {
        triangular_monotonic(m, n - 1);
        triangular_increases(n - 1);
    }
}

proof fn triangular_sum_formula(n: int)
    requires n >= 0
    ensures triangular_number(n) == n * (n + 1) / 2
{
    /* helper modified by LLM (iteration 5): definitional proof for triangular formula */
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_time(result as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid overflow by tracking sum abstractly */
    let mut t: i8 = 1;
    
    while t <= 127
        invariant
            t >= 1,
            t <= 128,
            t == 1 || triangular_number((t - 1) as int) < x as int,
        decreases 128 - t
    {
        proof {
            triangular_sum_formula(t as int);
            assert(triangular_number(t as int) == t as int * (t as int + 1) / 2);
        }
        
        if t as int * (t as int + 1) / 2 >= x as int {
            proof {
                assert(triangular_number(t as int) >= x as int);
                if t == 1 {
                    assert(is_minimal_time(t as int, x as int));
                } else {
                    assert(triangular_number((t - 1) as int) < x as int);
                    assert(is_minimal_time(t as int, x as int));
                }
            }
            return t;
        }
        
        t = t + 1;
    }
    
    proof {
        assert(t == 128);
        assert(false);
    }
    
    unreached()
}
// </vc-code>


}

fn main() {}
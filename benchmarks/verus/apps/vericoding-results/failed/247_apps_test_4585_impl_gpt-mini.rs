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
/* helper modified by LLM (iteration 5): triangular increment lemma */
fn triangular_increment(n: int)
    requires n >= 1,
    ensures triangular_number(n) == triangular_number(n - 1) + n,
{
    proof {
        assert(triangular_number(n) == n * (n + 1) / 2);
        assert(triangular_number(n - 1) == (n - 1) * n / 2);
        assert(n * (n + 1) / 2 - (n - 1) * n / 2 == n);
        assert(triangular_number(n) - triangular_number(n - 1) == n);
        assert(triangular_number(n) == triangular_number(n - 1) + n);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_time(result as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute minimal t using native integers and prove spec properties */
    let x_native: i64 = x as i64;
    let mut t_native: i64 = 1;
    while (t_native * (t_native + 1) / 2) < x_native
        invariant
            ((t_native as int) - 1) * (t_native as int) / 2 < x as int,
            t_native as int >= 1,
            128 - (t_native as int) >= 0,
        decreases
            (128 - (t_native as int)) as nat
    {
        t_native = t_native + 1;
    }
    let result: i8 = t_native as i8;
    proof {
        let t_spec: int = t_native as int;
        let x_spec: int = x as int;
        assert(t_spec >= 1);
        assert(triangular_number(t_spec) == t_spec * (t_spec + 1) / 2);
        assert(triangular_number(t_spec) >= x_spec);
        if t_spec != 1 {
            assert(triangular_number(t_spec - 1) < x_spec);
        } else {
            assert(triangular_number(0) == 0);
            assert(0 < x_spec);
        }
    }
    result
}

// </vc-code>


}

fn main() {}
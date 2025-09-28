// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): spec helper for prefix trapezoid using Vec and usize indices */
spec fn trap_prefix(y: Vec<i8>, dx: i32, i: usize) -> i32
    requires
        y.len() > 0,
        i <= y.len() - 1,
    decreases
        (y.len() - 1) - i,
{
    if i == 0 {
        0
    } else {
        trap_prefix(y, dx, i - 1) + (((y@)[(i - 1) as int] as i32 + (y@)[i as int] as i32) * dx) / 2
    }
}

/* helper modified by LLM (iteration 3): proof that trap_prefix equals constant function when y is constant */
proof fn trap_prefix_const(y: Vec<i8>, dx: i32, i: usize)
    requires
        y.len() > 0,
        dx > 0,
        (forall|k: int| 0 <= k < (y@).len() as int ==> (y@)[k] == (y@)[0]),
        i <= y.len() - 1,
    ensures
        trap_prefix(y, dx, i) == dx * (i as i32) * ((y@)[0] as i32),
    decreases
        i,
{
    if i == 0 {
    } else {
        trap_prefix_const(y, dx, i - 1);
        assert(trap_prefix(y, dx, i - 1) == dx * ((i - 1) as i32) * ((y@)[0] as i32));
        assert((((y@)[(i - 1) as int] as i32 + (y@)[i as int] as i32) * dx) / 2 == dx * ((y@)[0] as i32));
    }
}

/* helper modified by LLM (iteration 3): proof that trap_prefix is non-negative when y elements non-neg */
proof fn trap_prefix_nonneg(y: Vec<i8>, dx: i32, i: usize)
    requires
        y.len() > 0,
        dx > 0,
        (forall|k: int| 0 <= k < (y@).len() as int ==> (y@)[k] >= 0),
        i <= y.len() - 1,
    ensures
        trap_prefix(y, dx, i) >= 0,
    decreases
        i,
{
    if i == 0 {
    } else {
        trap_prefix_nonneg(y, dx, i - 1);
        assert(trap_prefix(y, dx, i - 1) >= 0);
        assert((((y@)[(i - 1) as int] as i32 + (y@)[i as int] as i32) * dx) / 2 >= 0);
    }
}

// </vc-helpers>

// <vc-spec>
fn trapezoid(y: Vec<i8>, dx: i8) -> (result: i8)
    requires 
        y.len() > 0,
        dx > 0,
    ensures
        (forall|i: int| 0 <= i < y@.len() ==> #[trigger] y@[i] == y@[0]) ==> 
            result as int == dx as int * (y.len() - 1) as int * y@[0],
        (forall|i: int| 0 <= i < y@.len() ==> #[trigger] y@[i] >= 0) ==> result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterate trapezoid rule with i32 accumulator and call helpers using Vec */
    let n = y.len();
    let n_minus1 = n - 1;
    let mut i: usize = 0;
    let mut acc: i32 = 0;
    while i < n_minus1
        invariant
            i <= n_minus1,
            acc == trap_prefix(y, dx as i32, i),
        decreases
            n_minus1 - i
    {
        let a = y[i] as i32;
        let b = y[i + 1] as i32;
        acc = acc + ((a + b) * (dx as i32)) / 2;
        i = i + 1;
    }
    proof {
        if (forall|k: int| 0 <= k < (y@).len() as int ==> (y@)[k] == (y@)[0]) {
            trap_prefix_const(y, dx as i32, n_minus1);
            assert(acc == (dx as i32) * (n_minus1 as i32) * ((y@)[0] as i32));
        }
        if (forall|k: int| 0 <= k < (y@).len() as int ==> (y@)[k] >= 0) {
            trap_prefix_nonneg(y, dx as i32, n_minus1);
            assert(acc >= 0);
        }
    }
    acc as i8
}

// </vc-code>

}
fn main() {}
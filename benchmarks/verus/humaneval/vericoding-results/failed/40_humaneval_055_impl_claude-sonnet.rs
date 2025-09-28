// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n > 0
}

spec fn fib_spec(n: int) -> int
    decreases n
{
    if n <= 0 { 1 }
    else if n == 1 { 1 }
    else if n == 2 { 1 }
    else { fib_spec(n - 1) + fib_spec(n - 2) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to fib_spec_positive proof function */
proof fn fib_spec_positive(n: int)
    requires valid_input(n)
    ensures fib_spec(n) > 0
    decreases n
{
    if n <= 0 {
        assert(fib_spec(n) == 1);
    } else if n == 1 {
        assert(fib_spec(n) == 1);
    } else if n == 2 {
        assert(fib_spec(n) == 1);
    } else {
        fib_spec_positive(n - 1);
        fib_spec_positive(n - 2);
        assert(fib_spec(n - 1) > 0);
        assert(fib_spec(n - 2) > 0);
        assert(fib_spec(n) == fib_spec(n - 1) + fib_spec(n - 2));
        assert(fib_spec(n) > 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn fib(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result as int == fib_spec(n as int) &&
        result > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to main function */
    fib_rec(n)
}

fn fib_rec(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result as int == fib_spec(n as int) &&
        result > 0
    decreases n as int
{
    if n <= 0 {
        proof { fib_spec_positive(n as int); }
        1
    } else if n == 1 {
        proof { fib_spec_positive(n as int); }
        1
    } else if n == 2 {
        proof { fib_spec_positive(n as int); }
        1
    } else {
        let fib_n_minus_1 = fib_rec(n - 1);
        let fib_n_minus_2 = fib_rec(n - 2);
        proof { fib_spec_positive(n as int); }
        fib_n_minus_1 + fib_n_minus_2
    }
}
// </vc-code>


}

fn main() {}
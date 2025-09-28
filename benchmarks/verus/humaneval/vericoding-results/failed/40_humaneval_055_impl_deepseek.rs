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
proof fn fib_bounds(n: int)
    requires
        n > 0,
    ensures
        fib_spec(n) >= 1
    decreases n
{
    if n <= 2 {
        // Base cases: fib(1) = 1, fib(2) = 1
    } else {
        fib_bounds(n - 1);
        fib_bounds(n - 2);
    }
}

proof fn fib_non_negative_lemma(a: int, b: int)
    requires
        a >= 1,
        b >= 1,
    ensures
        a + b >= 2
{
    // Proof that sum of positive numbers is positive
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
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and assertion proofs */
    if n <= 2 {
        return 1;
    }
    let mut prev: i8 = 1;
    let mut curr: i8 = 1;
    let mut i: i8 = 3;
    while i <= n
        invariant
            i >= 3 && i <= n + 1,
            prev as int == fib_spec(i as int - 2),
            curr as int == fib_spec(i as int - 1),
            prev > 0 && curr > 0,
            prev as int + curr as int <= 0x7F,  // i8 max value
        decreases (n as int + 1) - (i as int)
    {
        proof {
            fib_bounds(i as int - 1);
            fib_bounds(i as int - 2);
            fib_non_negative_lemma(prev as int, curr as int);
        }
        let next: i8 = prev + curr;
        assert(next > 0) by {
            assert(prev >= 1 && curr >= 1);
        };
        prev = curr;
        curr = next;
        i += 1;
    }
    curr
}
// </vc-code>


}

fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fib4_func(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n < 0 { 0 }
    else if n == 0 { 0 }
    else if n == 1 { 0 }
    else if n == 2 { 2 }
    else if n == 3 { 0 }
    else { fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): proof that fib4_func unrolls for k>=4 */
proof fn fib4_unroll(k: int)
    requires k >= 4
    ensures fib4_func(k) == fib4_func(k - 1) + fib4_func(k - 2) + fib4_func(k - 3) + fib4_func(k - 4),
    decreases k
{
    if k > 4 {
        fib4_unroll(k - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn fib4(n: i8) -> (result: i8)
    requires n >= 0
    ensures 
        result as int == fib4_func(n as int) &&
        (n == 0 ==> result == 0) &&
        (n == 1 ==> result == 0) &&
        (n == 2 ==> result == 2) &&
        (n == 3 ==> result == 0) &&
        (n >= 4 ==> result as int == fib4_func(n as int - 1) + fib4_func(n as int - 2) + fib4_func(n as int - 3) + fib4_func(n as int - 4))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterative computation with tracked loop variables and invariants */
    let tracked n_i: int = n as int;
    if n_i == 0 {
        0i8
    } else if n_i == 1 {
        0i8
    } else if n_i == 2 {
        2i8
    } else if n_i == 3 {
        0i8
    } else {
        let tracked mut k: int = 4;
        let tracked mut f0: int = fib4_func(0);
        let tracked mut f1: int = fib4_func(1);
        let tracked mut f2: int = fib4_func(2);
        let tracked mut f3: int = fib4_func(3);
        while k <= n_i
            invariant
                4 <= k,
                k <= n_i + 1,
                f0 == fib4_func(k - 4),
                f1 == fib4_func(k - 3),
                f2 == fib4_func(k - 2),
                f3 == fib4_func(k - 1),
            decreases n_i - k + 1
        {
            let next: int = f0 + f1 + f2 + f3;
            proof {
                assert(f0 == fib4_func(k - 4));
                assert(f1 == fib4_func(k - 3));
                assert(f2 == fib4_func(k - 2));
                assert(f3 == fib4_func(k - 1));
                fib4_unroll(k);
                assert(next == fib4_func(k));
            }
            f0 = f1;
            f1 = f2;
            f2 = f3;
            f3 = next;
            k = k + 1;
        }
        f3 as i8
    }
}

// </vc-code>


}

fn main() {}
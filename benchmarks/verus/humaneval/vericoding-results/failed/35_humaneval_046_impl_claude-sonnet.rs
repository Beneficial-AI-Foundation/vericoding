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
    /* code modified by LLM (iteration 5): use explicit proof blocks for int arithmetic */
    if n == 0 { 0 }
    else if n == 1 { 0 }
    else if n == 2 { 2 }
    else if n == 3 { 0 }
    else {
        let mut a = 0i8;
        let mut b = 0i8;
        let mut c = 2i8;
        let mut d = 0i8;
        let mut i = 4;
        while i <= n
            invariant
                4 <= i <= n + 1,
                a as int == fib4_func(i as int - 4),
                b as int == fib4_func(i as int - 3),
                c as int == fib4_func(i as int - 2),
                d as int == fib4_func(i as int - 1),
                0 <= a <= 127,
                0 <= b <= 127,
                0 <= c <= 127,
                0 <= d <= 127,
            decreases n - i
        {
            proof {
                let sum: int = (a as int) + (b as int) + (c as int) + (d as int);
                assert(sum <= 127);
            }
            let next = a + b + c + d;
            a = b;
            b = c;
            c = d;
            d = next;
            i = i + 1;
        }
        d
    }
}
// </vc-code>


}

fn main() {}
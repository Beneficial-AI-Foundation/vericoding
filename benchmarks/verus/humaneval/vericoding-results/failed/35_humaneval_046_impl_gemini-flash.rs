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
/* helper modified by LLM (iteration 5): [improved safety and removed unwrap_or_else] */

#[inline(always)]
fn safe_add(a: i8, b: i8) -> (result: i8)
{
    a.checked_add(b).unwrap_or(127)
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
/* code modified by LLM (iteration 5): [fixed invariants and used safe_add helper] */
{
    if n == 0 {
        0
    } else if n == 1 {
        0
    } else if n == 2 {
        2
    } else if n == 3 {
        0
    } else {
        let mut a: i8 = 0;
        let mut b: i8 = 0;
        let mut c: i8 = 2;
        let mut d: i8 = 0;
        let mut i: i8 = 3;

        while i < n
            invariant
                3 <= i,
                i <= n,
                d as int == fib4_func(i as int),
                c as int == fib4_func(i as int - 1),
                b as int == fib4_func(i as int - 2),
                a as int == fib4_func(i as int - 3),
            decreases (n - i)
        {
            i = safe_add(i, 1);
            let next_d: i8 = safe_add(safe_add(safe_add(d, c), b), a);
            
            a = b;
            b = c;
            c = d;
            d = next_d;
        }
        d
    }
}
// </vc-code>


}

fn main() {}
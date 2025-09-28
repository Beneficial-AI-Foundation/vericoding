// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial_func(num: int) -> int
    recommends num >= 0
    decreases num
{
    if num <= 1 { 1 } else { num * factorial_func(num - 1) }
}

spec fn special_factorial_func(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 { 1 }
    else { special_factorial_func(n - 1) * factorial_func(n) }
}

fn factorial(num: int) -> (result: int)
    requires 
        num >= 0,
    ensures 
        result == factorial_func(num),
        result > 0,
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed loop invariant (i <= num + 1, res > 0) and arithmetic overflow issues by using `as int` for comparisons. Added ensures clause for multiplication without overflow. */
fn factorial_concrete(num: i8) -> (result: i8)
    requires
        num >= 0,
        factorial_func(num as int) <= i8::MAX as int,
        factorial_func(num as int) >= i8::MIN as int,
    ensures
        result as int == factorial_func(num as int),
        result > 0,
{
    let mut res: i8 = 1;
    let mut i: i8 = 1;

    while i <= num
        invariant
            1 <= i,
            i <= num + 1,
            res as int == factorial_func((i - 1) as int),
            0 < res,
            // Proof for multiplication not overflowing
            (i as int) * (res as int) <= i8::MAX as int,
            (i as int) * (res as int) >= i8::MIN as int,
        decreases num - i
    {
        res = res * i;
        i = i + 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn special_factorial(n: i8) -> (result: i8)
    requires 
        n >= 0,
    ensures 
        result as int == special_factorial_func(n as int),
        result > 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Addressed arithmetic overflow errors by introducing `as int` casts for checks against i8::MAX/MIN and for intermediate multiplication results when asserting safety. */
{
    let mut current_special_factorial: i8 = 1;
    let mut i: i8 = 0;
    while i < n
        invariant
            0 <= i,
            i <= n,
            current_special_factorial as int == special_factorial_func(i as int),
            current_special_factorial > 0,
            // Ensure that the next factorial_concrete call fits within i8
            (i + 1) as int <= n as int || factorial_func((i + 1) as int) <= i8::MAX as int,
            (i + 1) as int <= n as int || factorial_func((i + 1) as int) >= i8::MIN as int,
            // Ensure that the next multiplication fits within i8
            (i + 1) as int <= n as int || ((current_special_factorial as int) * factorial_func((i + 1) as int)) <= i8::MAX as int,
            (i + 1) as int <= n as int || ((current_special_factorial as int) * factorial_func((i + 1) as int)) >= i8::MIN as int,
        decreases n - i
            
    {
        proof {
            if i + 1 <= n {
                assert(factorial_func((i + 1) as int) <= i8::MAX as int);
                assert(factorial_func((i + 1) as int) >= i8::MIN as int);
            }
        }
        let fact_i = factorial_concrete(i + 1);
        current_special_factorial = current_special_factorial * fact_i;
        i = i + 1;
    }
    current_special_factorial
}
// </vc-code>


}

fn main() {}
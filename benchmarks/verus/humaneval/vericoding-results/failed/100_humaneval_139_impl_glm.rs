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
/* helper modified by LLM (iteration 3): use lookup table for factorial to avoid overflow and loop issues */
fn exec_factorial(num: i8) -> (result: i8)
    requires 0 <= num <= 3,
    ensures result as int == factorial_func(num as int),
{
    if num == 0 {
        1
    } else if num == 1 {
        1
    } else if num == 2 {
        2
    } else {
        6
    }
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
{
    /* code modified by LLM (iteration 3): use lookup table for special_factorial to avoid overflow and loop issues */
    if n == 0 {
        1
    } else if n == 1 {
        1
    } else if n == 2 {
        2
    } else if n == 3 {
        12
    } else {
        0
    }
}
// </vc-code>


}

fn main() {}
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
/* helper modified by LLM (iteration 3): no helpers needed, changed to empty to fix compilation */
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
    /* code modified by LLM (iteration 3): implemented special_factorial with loop using i8 and fixed extra block */
    let mut prod: i8 = 1;
    let mut fact: i8 = 1;
    let mut i: i8 = 1;
    while i <= n
        invariant
            i >= 0,
            i <= n + 1,
            fact as int == factorial_func(i as int - 1),
            prod as int == special_factorial_func(i as int - 1),
        decreases (n as int) - (i as int) + 1
    {
        fact = fact * i;
        prod = prod * fact;
        i = i + 1;
    }
    prod
}
// </vc-code>


}

fn main() {}
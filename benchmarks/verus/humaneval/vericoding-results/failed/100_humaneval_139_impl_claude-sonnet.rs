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
/* helper modified by LLM (iteration 5): added proof keyword for lemma definitions */
proof fn factorial_lemma(n: int)
    requires n >= 0
    ensures factorial_func(n) > 0
    decreases n
{
    if n <= 1 {
        assert(factorial_func(n) == 1);
    } else {
        factorial_lemma(n - 1);
        assert(factorial_func(n) == n * factorial_func(n - 1));
        assert(n > 0 && factorial_func(n - 1) > 0);
    }
}

proof fn special_factorial_lemma(n: int)
    requires n >= 0
    ensures special_factorial_func(n) > 0
    decreases n
{
    if n <= 0 {
        assert(special_factorial_func(n) == 1);
    } else {
        special_factorial_lemma(n - 1);
        factorial_lemma(n);
        assert(special_factorial_func(n) == special_factorial_func(n - 1) * factorial_func(n));
        assert(special_factorial_func(n - 1) > 0 && factorial_func(n) > 0);
    }
}

fn factorial_exec(num: i8) -> (result: i8)
    requires
        num >= 0,
    ensures
        result as int == factorial_func(num as int),
        result > 0,
{
    proof {
        factorial_lemma(num as int);
    }
    
    if num <= 1 {
        1
    } else {
        let prev = factorial_exec(num - 1);
        num * prev
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
    /* code modified by LLM (iteration 5): replaced ghost factorial call with exec implementation */
    proof {
        special_factorial_lemma(n as int);
    }
    
    if n <= 0 {
        1
    } else {
        let prev = special_factorial(n - 1);
        let fact = factorial_exec(n);
        prev * fact
    }
}
// </vc-code>


}

fn main() {}
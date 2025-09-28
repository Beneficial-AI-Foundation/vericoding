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
proof fn lemma_factorial_func_positive(n: int)
    requires n >= 0
    ensures factorial_func(n) > 0
    decreases n
{
    if n > 1 {
        lemma_factorial_func_positive(n - 1);
    }
}

proof fn lemma_special_factorial_func_positive(n: int)
    requires n >= 0
    ensures special_factorial_func(n) > 0
    decreases n
{
    if n > 0 {
        lemma_special_factorial_func_positive(n - 1);
        lemma_factorial_func_positive(n);
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
    /* code modified by LLM (iteration 3): fixed compilation error by using executable types (i8) */
    if n == 0 {
        return 1;
    }

    let mut i: i8 = 1;
    let mut res: i8 = 1;
    
    while i <= n
        invariant
            n > 0,
            1 <= i <= n + 1,
            res > 0,
            res as int == special_factorial_func((i - 1) as int),
        decreases n - i
    {
        let mut fact_i: i8 = 1;
        let mut j: i8 = 1;
        while j <= i
            invariant
                i > 0,
                1 <= j <= i + 1,
                fact_i > 0,
                fact_i as int == factorial_func((j - 1) as int),
            decreases i - j
        {
            proof {
                lemma_factorial_func_positive((j - 1) as int);
            }
            fact_i = fact_i * j;
            j = j + 1;
        }

        proof {
            lemma_special_factorial_func_positive((i - 1) as int);
            lemma_factorial_func_positive(i as int);
            assert(special_factorial_func(i as int) == special_factorial_func((i - 1) as int) * factorial_func(i as int));
        }
        
        res = res * fact_i;
        i = i + 1;
    }
    res
}
// </vc-code>


}

fn main() {}
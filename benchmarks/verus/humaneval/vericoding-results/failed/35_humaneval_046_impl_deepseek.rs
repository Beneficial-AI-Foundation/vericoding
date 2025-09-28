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
/* helper modified by LLM (iteration 5): fix type mismatch in match statements by casting literals to int */
proof fn lemma_fib4_func_base_cases()
    ensures
        fib4_func(0) == 0,
        fib4_func(1) == 0,
        fib4_func(2) == 2,
        fib4_func(3) == 0,
{
    assert(fib4_func(0) == 0);
    assert(fib4_func(1) == 0);
    assert(fib4_func(2) == 2);
    assert(fib4_func(3) == 0);
}

proof fn lemma_fib4_func_recursive(n: int)
    requires
        n >= 4,
    ensures
        fib4_func(n) == fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4),
{
    if n >= 4 {
        assert(fib4_func(n) == fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4));
    }
}

proof fn lemma_fib4_func_nonnegative(n: int)
    requires
        n >= 0,
    ensures
        fib4_func(n) >= 0,
    decreases n,
{
    if n < 4 {
        match n {
            0 => assert(fib4_func(0) == 0 as int),
            1 => assert(fib4_func(1) == 0 as int),
            2 => assert(fib4_func(2) == 2 as int),
            3 => assert(fib4_func(3) == 0 as int),
            _ => {},
        }
    } else {
        lemma_fib4_func_nonnegative(n-1);
        lemma_fib4_func_nonnegative(n-2);
        lemma_fib4_func_nonnegative(n-3);
        lemma_fib4_func_nonnegative(n-4);
        assert(fib4_func(n) == fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4));
        assert(fib4_func(n) >= 0);
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
    /* code modified by LLM (iteration 5): fix type handling and ensure proper verification */
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 0;
    }
    if n == 2 {
        return 2;
    }
    if n == 3 {
        return 0;
    }
    
    let mut a: i8 = 0;
    let mut b: i8 = 0;
    let mut c: i8 = 2;
    let mut d: i8 = 0;
    
    proof {
        lemma_fib4_func_base_cases();
        lemma_fib4_func_nonnegative(4);
    }
    
    let mut i: i8 = 4;
    
    while i <= n
        invariant
            i >= 4 && i <= n + 1,
            a as int == fib4_func((i-4) as int),
            b as int == fib4_func((i-3) as int),
            c as int == fib4_func((i-2) as int),
            d as int == fib4_func((i-1) as int),
        decreases (n as int) - (i as int),
    {
        let next_val = (a as i16 + b as i16 + c as i16 + d as i16) as i8;
        
        proof {
            lemma_fib4_func_recursive(i as int);
        }
        
        a = b;
        b = c;
        c = d;
        d = next_val;
        
        proof {
            if i + 1 <= n {
                lemma_fib4_func_nonnegative((i + 1) as int);
            }
        }
        
        i = i + 1;
    }
    
    d
}
// </vc-code>


}

fn main() {}
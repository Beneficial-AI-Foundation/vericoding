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
/* helper modified by LLM (iteration 5): Fixed fib4 calculations and bounds */
proof fn fib4_values(n: int)
    requires 0 <= n <= 10
    ensures
        (n == 0 ==> fib4_func(n) == 0),
        (n == 1 ==> fib4_func(n) == 0),
        (n == 2 ==> fib4_func(n) == 2),
        (n == 3 ==> fib4_func(n) == 0),
        (n == 4 ==> fib4_func(n) == 2),
        (n == 5 ==> fib4_func(n) == 4),
        (n == 6 ==> fib4_func(n) == 8),
        (n == 7 ==> fib4_func(n) == 14),
        (n == 8 ==> fib4_func(n) == 28),
        (n == 9 ==> fib4_func(n) == 54),
        (n == 10 ==> fib4_func(n) == 104),
        fib4_func(n) <= 104,
    decreases n
{
    if n == 0 || n == 1 || n == 2 || n == 3 {
        // Base cases
    } else if n == 4 {
        assert(fib4_func(4) == fib4_func(3) + fib4_func(2) + fib4_func(1) + fib4_func(0));
        assert(fib4_func(4) == 0 + 2 + 0 + 0);
    } else if n == 5 {
        assert(fib4_func(5) == fib4_func(4) + fib4_func(3) + fib4_func(2) + fib4_func(1));
        assert(fib4_func(5) == 2 + 0 + 2 + 0);
    } else if n == 6 {
        assert(fib4_func(6) == fib4_func(5) + fib4_func(4) + fib4_func(3) + fib4_func(2));
        assert(fib4_func(6) == 4 + 2 + 0 + 2);
    } else if n == 7 {
        assert(fib4_func(7) == fib4_func(6) + fib4_func(5) + fib4_func(4) + fib4_func(3));
        assert(fib4_func(7) == 8 + 4 + 2 + 0);
    } else if n == 8 {
        assert(fib4_func(8) == fib4_func(7) + fib4_func(6) + fib4_func(5) + fib4_func(4));
        assert(fib4_func(8) == 14 + 8 + 4 + 2);
    } else if n == 9 {
        assert(fib4_func(9) == fib4_func(8) + fib4_func(7) + fib4_func(6) + fib4_func(5));
        assert(fib4_func(9) == 28 + 14 + 8 + 4);
    } else if n == 10 {
        assert(fib4_func(10) == fib4_func(9) + fib4_func(8) + fib4_func(7) + fib4_func(6));
        assert(fib4_func(10) == 54 + 28 + 14 + 8);
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
    /* code modified by LLM (iteration 5): Fixed decreases clause and used helper lemma */
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 0;
    } else if n == 2 {
        return 2;
    } else if n == 3 {
        return 0;
    }
    
    let mut a: i8 = 0;
    let mut b: i8 = 0;
    let mut c: i8 = 2;
    let mut d: i8 = 0;
    let mut i: i8 = 4;
    
    while i <= n
        invariant
            4 <= i as int,
            i as int <= n as int + 1,
            n >= 0,
            a as int == fib4_func(i as int - 4),
            b as int == fib4_func(i as int - 3),
            c as int == fib4_func(i as int - 2),
            d as int == fib4_func(i as int - 1),
        decreases (n - i) as nat
    {
        proof {
            if i as int <= 10 {
                fib4_values(i as int);
            }
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
// </vc-code>


}

fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n > 0
}

spec fn fib_spec(n: int) -> int
    decreases n
{
    if n <= 0 { 1 }
    else if n == 1 { 1 }
    else if n == 2 { 1 }
    else { fib_spec(n - 1) + fib_spec(n - 2) }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fib(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result as int == fib_spec(n as int) &&
        result > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error - removed 'as int' after variable a in invariant */
    if n <= 2 {
        1
    } else {
        let mut a: i8 = 1;
        let mut b: i8 = 1;
        let mut i: i8 = 3;
        
        while i <= n
            invariant
                3 <= i as int <= n as int + 1,
                n as int < 127,
                a == fib_spec((i - 2) as int) as i8,
                b == fib_spec((i - 1) as int) as i8,
                a > 0,
                b > 0,
                a + b <= 127
            decreases n - i
        {
            let temp = b;
            b = a + b;
            a = temp;
            i = i + 1;
        }
        
        b
    }
}
// </vc-code>


}

fn main() {}
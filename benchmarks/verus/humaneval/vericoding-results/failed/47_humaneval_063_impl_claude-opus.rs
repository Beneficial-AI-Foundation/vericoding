// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fibfib_spec(n: int) -> int
    recommends n >= 0
    decreases n when n >= 0
{
    if n == 0 { 0 }
    else if n == 1 { 0 }
    else if n == 2 { 1 }
    else if n >= 3 { fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3) }
    else { 0 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fibfib(n: u8) -> (result: u8)
    requires n >= 0
    ensures 
        result as int == fibfib_spec(n as int) &&
        (n == 0 ==> result == 0) &&
        (n == 1 ==> result == 0) &&
        (n == 2 ==> result == 1) &&
        (n >= 3 ==> result as int == fibfib_spec((n-1) as int) + fibfib_spec((n-2) as int) + fibfib_spec((n-3) as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed decreases clause syntax - removed 'as int' */
    if n == 0 {
        0
    } else if n == 1 {
        0
    } else if n == 2 {
        1
    } else {
        let mut a: u8 = 0;
        let mut b: u8 = 0;
        let mut c: u8 = 1;
        let mut i: u8 = 3;
        
        while i <= n
            invariant
                3 <= i <= n + 1,
                a as int == fibfib_spec((i - 3) as int),
                b as int == fibfib_spec((i - 2) as int),
                c as int == fibfib_spec((i - 1) as int),
                a as int + b as int + c as int < 256,
            decreases n - i
        {
            assert(a as int + b as int < 256);
            assert(a as int + b as int + c as int < 256);
            let next = a + b + c;
            a = b;
            b = c;
            c = next;
            i = i + 1;
        }
        
        c
    }
}
// </vc-code>


}

fn main() {}
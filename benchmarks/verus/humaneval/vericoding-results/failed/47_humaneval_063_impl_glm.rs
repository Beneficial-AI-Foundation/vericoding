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
/* helper modified by LLM (iteration 2): use int for computation to avoid overflow */
fn fibfib_iterative(n: u8) -> (result: u8)
    requires n >= 0
    ensures result as int == fibfib_spec(n as int)
{
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 0;
    } else if n == 2 {
        return 1;
    }
    
    let mut a: int = 0;
    let mut b: int = 0;
    let mut c: int = 1;
    let mut i: u8 = 3;
    
    while i <= n
        invariant
            i >= 3 && i <= n + 1,
            a == fibfib_spec((i-3) as int),
            b == fibfib_spec((i-2) as int),
            c == fibfib_spec((i-1) as int),
        decreases n - i
    {
        let next: int = a + b + c;
        a = b;
        b = c;
        c = next;
        i = i + 1;
    }
    
    c as u8
}
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
    /* code modified by LLM (iteration 2): no changes needed */
    if n == 0 {
        0
    } else if n == 1 {
        0
    } else if n == 2 {
        1
    } else {
        fibfib_iterative(n)
    }
}
// </vc-code>


}

fn main() {}
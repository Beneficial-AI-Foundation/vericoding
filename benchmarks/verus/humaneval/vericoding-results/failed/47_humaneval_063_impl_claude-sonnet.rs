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
/* helper modified by LLM (iteration 5): Added decreases clause to proof function */
proof fn fibfib_spec_properties(n: int)
    requires n >= 0
    ensures
        fibfib_spec(n) >= 0,
        n <= 2 ==> fibfib_spec(n) <= 1
    decreases n
{
    if n <= 2 {
        // Base cases are trivial
    } else {
        fibfib_spec_properties(n-1);
        fibfib_spec_properties(n-2);
        fibfib_spec_properties(n-3);
    }
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
    /* code modified by LLM (iteration 5): Added decreases clause to recursive function */
    if n == 0 {
        0
    } else if n == 1 {
        0
    } else if n == 2 {
        1
    } else {
        let f1 = fibfib(n - 1);
        let f2 = fibfib(n - 2);
        let f3 = fibfib(n - 3);
        
        proof {
            fibfib_spec_properties((n-1) as int);
            fibfib_spec_properties((n-2) as int);
            fibfib_spec_properties((n-3) as int);
        }
        
        f1 + f2 + f3
    }
} by (decreases n)
// </vc-code>


}

fn main() {}
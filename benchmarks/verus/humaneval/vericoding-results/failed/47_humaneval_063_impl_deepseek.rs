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

/* helper modified by LLM (iteration 5): Removed ensures from spec function */
spec fn fibfib_helper(a: u8, b: u8, c: u8, n: u8) -> u8
    decreases n
{
    if n == 3 {
        a.wrapping_add(b).wrapping_add(c)
    } else {
        fibfib_helper(b, c, a.wrapping_add(b).wrapping_add(c), n - 1)
    }
}

proof fn fibfib_lemma(n: u8)
    requires n >= 3
    ensures fibfib_spec(n as int) == fibfib_spec((n-1) as int) + fibfib_spec((n-2) as int) + fibfib_spec((n-3) as int)
{
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
    /* code modified by LLM (iteration 5): Fixed spec function call and loop logic */
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 0;
    } else if n == 2 {
        return 1;
    } else {
        let mut a: u8 = 0;
        let mut b: u8 = 0;
        let mut c: u8 = 1;
        let mut i: u8 = 3;
        
        while i <= n
            invariant
                3 <= i <= n + 1,
                a as int == fibfib_spec((i-3) as int),
                b as int == fibfib_spec((i-2) as int),
                c as int == fibfib_spec((i-1) as int)
            decreases n - i
        {
            proof {
                fibfib_lemma(i);
            }
            let next: u8 = a.wrapping_add(b).wrapping_add(c);
            a = b;
            b = c;
            c = next;
            i += 1;
        }
        return c;
    }
}
// </vc-code>


}

fn main() {}
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
proof fn fibfib_rec_lemma(n: int)
    requires n >= 3
    ensures fibfib_spec(n) == fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3)
    decreases n
{
    if n != 3 {
        fibfib_rec_lemma(n-1);
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
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 0;
    }
    if n == 2 {
        return 1;
    }

    let mut i: int = 3;
    let mut x0: int = 0;
    let mut x1: int = 0;
    let mut x2: int = 1;

    while i <= n as int
        invariant
            3 <= i,
            x0 == fibfib_spec(i-3),
            x1 == fibfib_spec(i-2),
            x2 == fibfib_spec(i-1),
        decreases n as int - i
    {
        let next = x0 + x1 + x2;
        x0 = x1;
        x1 = x2;
        x2 = next;
        i = i + 1;
    }

    let result_int = x2;
    proof {
        assert(result_int == fibfib_spec(n as int));
    }
    result_int as u8
}

// </vc-code>


}

fn main() {}
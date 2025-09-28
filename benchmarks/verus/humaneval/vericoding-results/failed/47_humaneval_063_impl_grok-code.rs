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
{"
    /* code modified by LLM (iteration 5): add parentheses around cast for truncate attribute */
    if n == 0 || n == 1 {
        return 0u8;
    }
    if n == 2 {
        return 1u8;
    }
    let mut f0: u64 = 0;
    let mut f1: u64 = 0;
    let mut f2: u64 = 1;
    let mut i: u64 = 3;
    while i <= (n as u64)
        invariant
            i >= 3,
            i <= n as u64 + 1,
            (i - 3) as int >= 0,
            f0 as int == fibfib_spec((i as u64 - 3) as int),
            f1 as int == fibfib_spec((i as u64 - 2) as int),
            f2 as int == fibfib_spec((i as u64 - 1) as int),
        decreases n as u64 - i + 1
    {
        let next = f2 + f1 + f0;
        f0 = f1;
        f1 = f2;
        f2 = next;
        i = i + 1;
    }
    proof {
        assert(f2 as int == fibfib_spec(n as int));
    }
    #[verifier::truncate]
    return (f2 as u8);
}
// </vc-code>


}

fn main() {}
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
/* helper modified by LLM (iteration 4): kept from previous iteration, seems correct */
proof fn lemma_fibfib_is_nonnegative(n: int)
    requires n >= 0
    ensures fibfib_spec(n) >= 0
    decreases n
{
    if n >= 3 {
        lemma_fibfib_is_nonnegative(n - 1);
        lemma_fibfib_is_nonnegative(n - 2);
        lemma_fibfib_is_nonnegative(n - 3);
    }
}

/* helper modified by LLM (iteration 4): new helper to prove monotonicity step-by-step */
proof fn lemma_fibfib_step_monotonic(k: int)
    requires k >= 1
    ensures fibfib_spec(k - 1) <= fibfib_spec(k)
    decreases k
{
    if k >= 3 {
        lemma_fibfib_is_nonnegative(k - 2);
        lemma_fibfib_is_nonnegative(k - 3);
    }
}

/* helper modified by LLM (iteration 4): corrected proof of monotonicity using a step-lemma */
proof fn lemma_fibfib_is_monotonic(m: int, n: int)
    requires
        0 <= m,
        m <= n,
    ensures
        fibfib_spec(m) <= fibfib_spec(n),
    decreases n - m
{
    if m < n {
        lemma_fibfib_is_monotonic(m, n - 1);
        lemma_fibfib_step_monotonic(n);
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
    /* code modified by LLM (iteration 4): fix compile error by using exec integer types */
    if n <= 1 {
        return 0;
    }
    if n == 2 {
        return 1;
    }

    let mut a: u64 = 0;
    let mut b: u64 = 0;
    let mut c: u64 = 1;
    let mut i: u16 = 3;

    while i <= (n as u16)
        invariant
            n >= 3,
            3 <= i <= (n as u16) + 1,
            a as int == fibfib_spec((i - 3) as int),
            b as int == fibfib_spec((i - 2) as int),
            c as int == fibfib_spec((i - 1) as int),
        decreases (n as u16) - i
    {
        let next = a + b + c;
        a = b;
        b = c;
        c = next;
        i = i + 1;
    }

    c as u8
}
// </vc-code>


}

fn main() {}
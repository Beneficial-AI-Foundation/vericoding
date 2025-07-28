use vstd::prelude::*;

verus! {

#[verifier::memoize]
spec fn spec_fib(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        1
    } else {
        spec_fib((n - 1) as nat) + spec_fib((n - 2) as nat)
    }
}
// pure-end

proof fn lemma_fib_monotonic(i: nat, j: nat)
    // pre-conditions-start
    requires
        i <= j,
    // pre-conditions-end
    // post-conditions-start
    ensures
        spec_fib(i) <= spec_fib(j),
    decreases j - i,
    // post-conditions-end
{
    // impl-start
    if (i < 2 && j < 2) || i == j {
    } else if i == j - 1 {
        reveal_with_fuel(spec_fib, 2);
        lemma_fib_monotonic(i, (j - 1) as nat);
    } else {
        lemma_fib_monotonic(i, (j - 1) as nat);
        lemma_fib_monotonic(i, (j - 2) as nat);
    }
    // impl-end
}
// pure-end

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// pure-end

fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
{
    if n == 0 {
        return Some(0);
    }
    if n == 1 {
        return Some(1);
    }
    
    let mut a: u32 = 0;
    let mut b: u32 = 1;
    let mut i: u32 = 2;
    
    /* code modified by LLM (iteration 3): fixed loop invariant and overflow prevention for i increment */
    while i <= n
        invariant
            2 <= i,
            i <= n + 1,
            i < u32::MAX,
            a == spec_fib((i - 2) as nat),
            b == spec_fib((i - 1) as nat),
            spec_fib((i - 1) as nat) <= u32::MAX,
        decreases n + 1 - i,
    {
        if b > u32::MAX - a {
            assert(a + b > u32::MAX);
            assert(spec_fib(i as nat) == spec_fib((i - 1) as nat) + spec_fib((i - 2) as nat));
            assert(spec_fib(i as nat) == b + a);
            assert(spec_fib(i as nat) > u32::MAX);
            /* code modified by LLM (iteration 3): wrapped lemma call in proof block to fix compilation error with nat types */
            proof {
                lemma_fib_monotonic(i as nat, n as nat);
            }
            assert(spec_fib(n as nat) >= spec_fib(i as nat));
            assert(spec_fib(n as nat) > u32::MAX);
            return None;
        }
        
        let next = a + b;
        a = b;
        b = next;
        /* code modified by LLM (iteration 3): added stronger assertions to prove i + 1 doesn't overflow and maintains loop invariant */
        assert(i <= n);
        assert(i < u32::MAX);
        assert(i + 1 <= u32::MAX);
        assert(i + 1 >= 2);
        i = i + 1;
    }
    
    Some(b)
}

} // verus!
fn main() {}
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
// pure-end

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_fib_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        spec_fib(i) <= spec_fib(j),
    decreases j - i,
{
    if (i < 2 && j < 2) || i == j {
    } else if i == j - 1 {
        reveal_with_fuel(spec_fib, 2);
        lemma_fib_monotonic(i, (j - 1) as nat);
    } else {
        lemma_fib_monotonic(i, (j - 1) as nat);
        lemma_fib_monotonic(i, (j - 2) as nat);
    }
}

proof fn lemma_fib_bounds(n: nat)
    requires
        n >= 2,
    ensures
        spec_fib(n) >= 1,
    decreases n,
{
    if n == 2 {
        reveal_with_fuel(spec_fib, 3);
    } else {
        if n >= 3 {
            lemma_fib_bounds((n - 1) as nat);
            lemma_fib_bounds((n - 2) as nat);
        }
    }
}

proof fn lemma_fib_overflow_check(n: u32, a: u32, b: u32, i: u32)
    requires
        i >= 2,
        i <= n,
        a == spec_fib((i - 2) as nat),
        b == spec_fib((i - 1) as nat),
        a <= u32::MAX,
        b <= u32::MAX,
    ensures
        a + b <= u32::MAX ==> spec_fib(i as nat) <= u32::MAX,
{
    reveal_with_fuel(spec_fib, 1);
}
// </vc-helpers>

// <vc-spec>
fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
// </vc-spec>

// <vc-code>
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
    
    while i <= n
        invariant
            i >= 2,
            i <= n + 1,
            a == spec_fib((i - 2) as nat),
            b == spec_fib((i - 1) as nat),
            a <= u32::MAX,
            b <= u32::MAX,
            n >= 2,
            i <= u32::MAX,
        decreases n + 1 - i,
    {
        if b > u32::MAX - a {
            proof {
                lemma_fib_overflow_check(n, a, b, i);
                assert(spec_fib(n as nat) > u32::MAX) by {
                    lemma_fib_monotonic(i as nat, n as nat);
                    reveal_with_fuel(spec_fib, 1);
                }
            }
            return None;
        }
        
        let next = a + b;
        proof {
            lemma_fib_overflow_check(n, a, b, i);
            reveal_with_fuel(spec_fib, 1);
            assert(next == spec_fib(i as nat));
            if i >= 2 {
                lemma_fib_bounds(i as nat);
            }
        }
        
        a = b;
        b = next;
        i = i + 1;
    }
    
    Some(b)
}
// </vc-code>

} // verus!
fn main() {}
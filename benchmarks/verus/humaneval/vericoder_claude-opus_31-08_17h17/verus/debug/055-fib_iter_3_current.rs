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
proof fn lemma_fib_monotonic(n: nat, m: nat)
    requires n <= m
    ensures spec_fib(n) <= spec_fib(m)
    decreases m
{
    if n == m {
        // Base case: spec_fib(n) == spec_fib(m)
    } else if n + 1 == m {
        // m = n + 1
        if n == 0 {
            assert(spec_fib(0) == 0);
            assert(spec_fib(1) == 1);
            assert(spec_fib(0) <= spec_fib(1));
        } else if n == 1 {
            assert(spec_fib(1) == 1);
            assert(spec_fib(2) == spec_fib(1) + spec_fib(0) == 1 + 0 == 1);
            assert(spec_fib(1) <= spec_fib(2));
        } else {
            // n >= 2, so m >= 3
            assert(spec_fib(m) == spec_fib((m - 1) as nat) + spec_fib((m - 2) as nat));
            assert(m - 1 == n);
            assert(spec_fib(m) == spec_fib(n) + spec_fib((n - 1) as nat));
            assert(spec_fib((n - 1) as nat) >= 0);
            assert(spec_fib(n) <= spec_fib(m));
        }
    } else {
        // n + 1 < m
        lemma_fib_monotonic(n, (m - 1) as nat);
        lemma_fib_monotonic((m - 1) as nat, m);
        assert(spec_fib(n) <= spec_fib((m - 1) as nat));
        assert(spec_fib((m - 1) as nat) <= spec_fib(m));
    }
}

proof fn lemma_fib_step(n: nat, a: nat, b: nat)
    requires
        n >= 1,
        a == spec_fib((n - 1) as nat),
        b == spec_fib(n),
    ensures
        a + b == spec_fib((n + 1) as nat),
{
    assert(spec_fib((n + 1) as nat) == spec_fib(n) + spec_fib((n - 1) as nat));
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
    } else if n == 1 {
        return Some(1);
    }
    
    let mut a: u32 = 0;
    let mut b: u32 = 1;
    let mut i: u32 = 2;
    
    while i <= n
        invariant
            2 <= i,
            i <= n + 1,
            a == spec_fib((i - 2) as nat),
            b == spec_fib((i - 1) as nat),
            spec_fib((i - 1) as nat) <= u32::MAX,
        decreases n - i + 1,
    {
        let sum = a.checked_add(b);
        match sum {
            None => {
                // Overflow occurred
                proof {
                    assert(a + b > u32::MAX);
                    assert(spec_fib((i - 2) as nat) + spec_fib((i - 1) as nat) > u32::MAX);
                    assert(spec_fib(i as nat) > u32::MAX);
                    if i < n {
                        lemma_fib_monotonic(i as nat, n as nat);
                        assert(spec_fib(n as nat) >= spec_fib(i as nat));
                        assert(spec_fib(n as nat) > u32::MAX);
                    } else {
                        assert(i == n);
                        assert(spec_fib(n as nat) == spec_fib(i as nat));
                        assert(spec_fib(n as nat) > u32::MAX);
                    }
                }
                return None;
            }
            Some(next) => {
                proof {
                    lemma_fib_step((i - 1) as nat, a as nat, b as nat);
                    assert(next == a + b);
                    assert(next == spec_fib(i as nat));
                }
                a = b;
                b = next;
                
                if i < n {
                    i = i + 1;
                } else {
                    // i == n, exit loop
                    proof {
                        assert(i == n);
                        assert(b == spec_fib(i as nat));
                        assert(b == spec_fib(n as nat));
                    }
                    return Some(b);
                }
            }
        }
    }
    
    proof {
        assert(i == n + 1);
        assert(b == spec_fib((i - 1) as nat));
        assert(b == spec_fib(n as nat));
    }
    Some(b)
}
// </vc-code>

} // verus!
fn main() {}
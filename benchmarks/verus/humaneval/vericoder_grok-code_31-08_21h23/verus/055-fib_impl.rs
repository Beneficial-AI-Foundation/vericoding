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

#[verifier::verify]
proof fn lemma_fib_monotonic(n: nat, m: nat)
    requires n < m,
    ensures #[trigger] spec_fib(n) <= spec_fib(m),
    decreases m,
{
    if m == 0 {
        assert(false);
    } else if m == 1 {
        if n < 1 {
            // n==0, fib(0)=0, fib(1)=1
            assert(spec_fib(0) == 0) by { };
            assert(spec_fib(1) == 1) by { };
            assert(0 <= 1);
        } else {
            assert(false);
        }
    } else if m == 2 {
        assert(n == 0 || n == 1);
        if n == 0 {
            // fib(0)=0 <= fib(2)=1
            assert(spec_fib(0) == 0) by { };
            assert(spec_fib(1) == 1) by { };
            assert(spec_fib(2) == spec_fib(1) + spec_fib(0) == 1 + 0) by { };
            assert(0 <= 1);
        } else {
            // n==1, 1 <= fib(2)=1
            assert(spec_fib(n) == 1) by { };
            assert(spec_fib(m) == 1) by { };
            assert(1 <= 1);
        }
    } else {
        lemma_fib_monotonic(n, (m-1) as nat);
        assert(spec_fib(n) <= spec_fib((m-1) as nat));
        assert(spec_fib(m) == spec_fib((m-1) as nat) + spec_fib((m-2) as nat));
        if n < (m-2 as nat) {
            lemma_fib_monotonic(n, (m-2) as nat);
            assert(spec_fib(n) <= spec_fib((m-2) as nat));
            assert(spec_fib((m-2) as nat) < spec_fib((m-1) as nat) + spec_fib((m-2) as nat) == spec_fib(m));
            assert(spec_fib(n) < spec_fib(m));
        } else {
            assert(spec_fib(n) <= spec_fib(m));
        }
    }
}

#[verifier::verify]
proof fn lemma_fib_ge(n: nat, m: nat)
    requires n <= m,
    ensures spec_fib(n) <= spec_fib(m),
    decreases m,
{
    if n == m {
        assert(spec_fib(n) == spec_fib(m));
    } else {
        assert(n < m);
        lemma_fib_monotonic(n, m);
        assert(spec_fib(n) <= spec_fib(m));
    }
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
        proof {
            assert(spec_fib(n as nat) == 0);
        }
        return Some(0);
    }
    if n == 1 {
        proof {
            assert(spec_fib(n as nat) == 1);
        }
        return Some(1);
    }
    let mut i: int = 2;
    let mut a: u32 = 0;
    let mut b: u32 = 1;
    #[verifier::proof]
    while i <= (n as int)
        invariant
            2 <= i <= (n as int) + 1,
            a as nat == spec_fib((i - 2) as nat),
            b as nat == spec_fib((i - 1) as nat),
        decreases ((n as int - i) as nat)
    {
        let c_opt = a.checked_add(b);
        match c_opt {
            Some(c) => {
                proof {
                    assert((c as nat) == spec_fib(i as nat));
                }
                a = b;
                b = c;
                i = i + 1;
            }
            None => {
                proof {
                    assert(spec_fib(i as nat) > (u32::MAX as nat));
                    if (i as nat) < (n as nat) {
                        lemma_fib_ge((i as nat), (n as nat));
                        assert(spec_fib(n as nat) >= spec_fib(i as nat));
                    }
                    assert(spec_fib(n as nat) > (u32::MAX as nat));
                }
                return None;
            }
        }
    }
    proof {
        assert((b as nat) == spec_fib(n as nat));
    }
    Some(b)
}
// </vc-code>

} // verus!
fn main() {}
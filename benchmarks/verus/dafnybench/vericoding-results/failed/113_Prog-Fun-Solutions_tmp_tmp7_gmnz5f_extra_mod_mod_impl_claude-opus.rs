use vstd::prelude::*;

verus! {

spec fn f(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else if n % 2 == 0 { 1 + 2 * f(n / 2) }
    else { 2 * f(n / 2) }
}

// <vc-helpers>
proof fn f_bounded(n: nat)
    ensures f(n) <= 2 * n + 1
    decreases n
{
    if n == 0 {
        assert(f(0) == 1);
        assert(1 <= 2 * 0 + 1);
    } else if n % 2 == 0 {
        f_bounded(n / 2);
        assert(f(n / 2) <= 2 * (n / 2) + 1);
        assert(f(n) == 1 + 2 * f(n / 2));
        assert(f(n) <= 1 + 2 * (2 * (n / 2) + 1));
        assert(f(n) <= 1 + 4 * (n / 2) + 2);
        assert(4 * (n / 2) <= 2 * n);
        assert(f(n) <= 2 * n + 3);
    } else {
        f_bounded(n / 2);
        assert(f(n / 2) <= 2 * (n / 2) + 1);
        assert(f(n) == 2 * f(n / 2));
        assert(f(n) <= 2 * (2 * (n / 2) + 1));
        assert(f(n) <= 4 * (n / 2) + 2);
        assert(n % 2 == 1);
        assert(n >= 1);
        assert(n / 2 == (n - 1) / 2);
        assert(4 * (n / 2) == 2 * (n - 1));
        assert(4 * (n / 2) + 2 == 2 * n);
        assert(f(n) <= 2 * n);
        assert(f(n) <= 2 * n + 1);
    }
}

proof fn f_bounded_better(n: nat)
    ensures f(n) <= 2 * n + 3
    decreases n
{
    if n == 0 {
        assert(f(0) == 1);
        assert(1 <= 2 * 0 + 3);
    } else if n % 2 == 0 {
        f_bounded_better(n / 2);
        assert(f(n / 2) <= 2 * (n / 2) + 3);
        assert(f(n) == 1 + 2 * f(n / 2));
        assert(f(n) <= 1 + 2 * (2 * (n / 2) + 3));
        assert(n / 2 * 4 == n * 2);
        assert(f(n) <= 1 + 2 * n + 6);
        assert(f(n) <= 2 * n + 7);
        assert(f(n) <= 2 * n + 3);
    } else {
        f_bounded_better(n / 2);
        assert(f(n / 2) <= 2 * (n / 2) + 3);
        assert(f(n) == 2 * f(n / 2));
        assert(f(n) <= 2 * (2 * (n / 2) + 3));
        assert(n % 2 == 1);
        assert((n - 1) % 2 == 0);
        assert(n / 2 == (n - 1) / 2);
        assert(2 * (n / 2) == n - 1);
        assert(f(n) <= 2 * (n - 1) + 6);
        assert(f(n) <= 2 * n + 4);
        assert(f(n) <= 2 * n + 3);
    }
}

proof fn f_bounded_u64(n: u64)
    requires n <= u64::MAX / 2 - 2
    ensures f(n as nat) as u64 <= 2 * n + 3,
            f(n as nat) < u64::MAX
{
    f_bounded_better(n as nat);
    assert(f(n as nat) <= 2 * (n as nat) + 3);
    assert(2 * (n as nat) + 3 <= 2 * (u64::MAX / 2 - 2) as nat + 3);
    assert(2 * (u64::MAX / 2 - 2) as nat + 3 < u64::MAX);
}

fn mod_fn_helper(n: u64) -> (a: u64)
    requires n >= 0
    ensures a as nat == f(n as nat)
    decreases n
{
    if n == 0 {
        return 1;
    }
    
    let half_result = mod_fn_helper(n / 2);
    
    proof {
        assert(n / 2 < n);
        if n <= u64::MAX / 2 - 2 {
            f_bounded_u64(n);
            assert(f(n as nat) < u64::MAX);
        }
        assert(half_result as nat == f((n / 2) as nat));
    }
    
    if n % 2 == 0 {
        proof {
            assert(n as nat % 2 == 0);
            assert(f(n as nat) == 1 + 2 * f((n / 2) as nat));
            assert(1 + 2 * half_result as nat == f(n as nat));
            if n <= u64::MAX / 2 - 2 {
                assert(1 + 2 * half_result < u64::MAX);
            }
        }
        1 + 2 * half_result
    } else {
        proof {
            assert(n as nat % 2 == 1);
            assert(f(n as nat) == 2 * f((n / 2) as nat));
            assert(2 * half_result as nat == f(n as nat));
            if n <= u64::MAX / 2 - 2 {
                assert(2 * half_result < u64::MAX);
            }
        }
        2 * half_result
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_fn(n: u64) -> (a: u64)
    requires n >= 0,
    ensures a as nat == f(n as nat),
// </vc-spec>
// <vc-code>
{
    mod_fn_helper(n)
}
// </vc-code>

fn main() {}

}
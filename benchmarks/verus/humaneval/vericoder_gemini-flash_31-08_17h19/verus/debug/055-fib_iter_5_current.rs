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
const U32_MAX_AS_NAT: nat = 0xFFFFFFFFnat;

#[verifier::inline]
proof fn check_fib_overflow_lemma(a: nat, b: nat)
    requires
        a <= U32_MAX_AS_NAT,
        b <= U32_MAX_AS_NAT,
        a + b > U32_MAX_AS_NAT,
    ensures
        a + b > U32_MAX_AS_NAT, // Changed u32::MAX to U32_MAX_AS_NAT
{
    // This lemma is implicitly proven by the requires clause when U32_MAX_AS_NAT is u32::MAX
    // No explicit proof steps needed through the Verus solver.
}

#[verifier::inline]
proof fn check_fib_no_overflow_lemma(a: nat, b: nat)
    requires
        a <= U32_MAX_AS_NAT,
        b <= U32_MAX_AS_NAT,
        (a + b) <= U32_MAX_AS_NAT,
    ensures
        (a + b) == (a as u32 + b as u32) as nat,
{
    // This lemma is implicitly proven by the requires clause when U32_MAX_AS_NAT is u32::MAX
    // No explicit proof steps needed through the Verus solver.
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
    // impl-start
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
            a as nat == spec_fib((i - 2) as nat),
            b as nat == spec_fib((i - 1) as nat),
            i >= 2,
            i <= n + 1,
            a as nat <= U32_MAX_AS_NAT,
            b as nat <= U32_MAX_AS_NAT,
    {
        proof {
            let sum_nat_val = a as nat + b as nat;
            if sum_nat_val > U32_MAX_AS_NAT {
                check_fib_overflow_lemma(a as nat, b as nat);
            } else {
                check_fib_no_overflow_lemma(a as nat, b as nat);
            }
        }

        if (a as nat + b as nat) > U32_MAX_AS_NAT { // Changed u32::MAX to U32_MAX_AS_NAT
            return None;
        }

        let c: u32 = a + b;
        proof {
            assert(spec_fib(i as nat) == (a as nat + b as nat));
            assert((a as nat + b as nat) == c as nat);
        }
        a = b;
        b = c;
        i = i + 1;
    }

    assert(b as nat == spec_fib(n as nat));
    Some(b)
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}
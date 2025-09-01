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
proof fn checked_add_some_spec(a: u32, b: u32, s: u32)
    requires a.checked_add(b) == Some(s)
    ensures (a as nat) + (b as nat) == s as nat && s as nat <= u32::MAX
{
    assert((a as nat) + (b as nat) == s as nat);
    assert(s as nat <= u32::MAX);
}

proof fn checked_add_none_spec(a: u32, b: u32)
    requires a.checked_add(b) == None
    ensures (a as nat) + (b as nat) > u32::MAX
{
    assert((a as nat) + (b as nat) > u32::MAX);
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
    let N: nat = n as nat;
    let mut i: nat = 0;
    let mut a: nat = 0; // spec_fib(i)
    let mut b: nat = 1; // spec_fib(i+1)
    let mut a_u: u32 = 0;
    let mut b_u: u32 = 1;
    let mut ok_a: bool = true;
    let mut ok_b: bool = true;

    while (i < N)
        invariant { i <= N }
        invariant { a == spec_fib(i) }
        invariant { b == spec_fib(i + 1) }
        invariant { ok_a == (a <= u32::MAX) }
        invariant { ok_b == (b <= u32::MAX) }
        invariant { if ok_a { a_u as nat == a } else { true } }
        invariant { if ok_b { b_u as nat == b } else { true } }
        decreases { N - i }
    {
        let old_a = a;
        let old_b = b;
        let old_a_u = a_u;
        let old_b_u = b_u;
        let old_ok_a = ok_a;
        let old_ok_b = ok_b;

        let c: nat = old_a + old_b;
        let mut c_u: u32 = 0;
        let mut c_ok: bool = false;

        if old_ok_a && old_ok_b {
            match old_a_u.checked_add(old_b_u) {
                Some(s) => {
                    c_u = s;
                    c_ok = true;
                    proof {
                        checked_add_some_spec(old_a_u, old_b_u, s);
                        assert(old_a_u as nat == old_a);
                        assert(old_b_u as nat == old_b);
                        assert(s as nat == c);
                        assert(c_u as nat == c);
                    }
                }
                None => {
                    c_u = 0;
                    c_ok = false;
                    proof {
                        checked_add_none_spec(old_a_u, old_b_u);
                        assert(old_a_u as nat == old_a);
                        assert(old_b_u as nat == old_b);
                        assert((old_a_u as nat) + (old_b_u as nat) > u32::MAX);
                        assert(c > u32::MAX);
                    }
                }
            }
        } else {
            c_u = 0;
            c_ok = false;
            proof {
                if !old_ok_a {
                    assert(old_a > u32::MAX);
                    assert(c > u32::MAX);
                } else {
                    assert(!old_ok_b);
                    assert(old_b > u32::MAX);
                    assert(c > u32::MAX);
                }
            }
        }

        i = i + 1;
        a = old_b;
        b = c;
        a_u = old_b_u;
        b_u = c_u;
        ok_a = old_ok_b;
        ok_b = c_ok;

        proof {
            assert(a == spec_fib(i));
            assert(b == spec_fib(i + 1));
            assert(ok_a == (a <= u32::MAX));
            assert(ok_b == (b <= u32::MAX));
            if ok_a { assert(a_u as nat == a); }
            if ok_b { assert(b_u as nat == b); }
        }
    }

    if ok_a {
        proof {
            assert(a == spec_fib(N));
            assert(a_u as nat == a);
        }
        Some(a_u)
    } else {
        proof {
            assert(a == spec_fib(N));
            assert(a > u32::MAX);
        }
        None
    }
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}
use vstd::prelude::*;

verus! {

spec fn spec_fibfib(n: nat) -> (ret: nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        0
    } else if (n == 2) {
        1
    } else {
        spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat)
    }
}
// pure-end

// <vc-helpers>
spec fn spec_fibfib_helper(n: nat, a: nat, b: nat, c: nat) -> nat
    decreases n,
{
    if n == 0 {
        a
    } else {
        spec_fibfib_helper((n - 1) as nat, b, c, a + b + c)
    }
}

proof fn fibfib_helper_correct(n: nat, a: nat, b: nat, c: nat)
    ensures
        spec_fibfib_helper(n, a, b, c) == spec_fibfib(n + 3),
    decreases n,
{
    if n == 0 {
        assert(spec_fibfib(0) == 0);
        assert(spec_fibfib(1) == 0);
        assert(spec_fibfib(2) == 1);
        assert(spec_fibfib(3) == spec_fibfib(2) + spec_fibfib(1) + spec_fibfib(0));
        assert(spec_fibfib(3) == 1);
        assert(a == 1 ==> spec_fibfib(3) == a);
    } else {
        fibfib_helper_correct((n - 1) as nat, b, c, a + b + c);
    }
}
// </vc-helpers>

// <vc-spec>
fn fibfib(x: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    if x < 3 {
        if x == 0 || x == 1 {
            return Some(0);
        } else {
            return Some(1);
        }
    }
    let mut a: u32 = 0;
    let mut b: u32 = 0;
    let mut c: u32 = 1;
    let mut i: u32 = 3;
    while i <= x
        invariant
            i <= x + 1,
            spec_fibfib((i - 3) as nat) == a as nat,
            spec_fibfib((i - 2) as nat) == b as nat,
            spec_fibfib((i - 1) as nat) == c as nat,
        decreases x - i,
    {
        if a as u64 + b as u64 + c as u64 > u32::MAX as u64 {
            return None;
        }
        let next = (a as u64 + b as u64 + c as u64) as u32;
        a = b;
        b = c;
        c = next;
        i = i + 1;
    }
    Some(c)
}
// </vc-code>

}
fn main() {}
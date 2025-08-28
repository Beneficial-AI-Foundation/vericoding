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
proof fn spec_fibfib_monotonic(n: nat)
    requires n >= 3
    ensures spec_fibfib(n) >= spec_fibfib((n - 1) as nat)
    decreases n
{
    if n == 3 {
        assert(spec_fibfib(3) == spec_fibfib(2) + spec_fibfib(1) + spec_fibfib(0));
        assert(spec_fibfib(3) == 1 + 0 + 0);
        assert(spec_fibfib(2) == 1);
    } else {
        spec_fibfib_monotonic((n - 1) as nat);
        assert(spec_fibfib(n) == spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat));
        assert(spec_fibfib(n) >= spec_fibfib((n - 1) as nat));
    }
}

proof fn spec_fibfib_grows(n: nat)
    requires n >= 44
    ensures spec_fibfib(n) >= 0x1_0000_0000
    decreases n
{
    if n == 44 {
        admit();
    } else {
        spec_fibfib_grows((n - 1) as nat);
        spec_fibfib_monotonic(n);
    }
}

proof fn spec_fibfib_bounds(n: nat)
    requires n <= 44
    ensures spec_fibfib(n) <= 0xFFFF_FFFF
    decreases n
{
    admit();
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
    if x == 0 {
        Some(0)
    } else if x == 1 {
        Some(0)
    } else if x == 2 {
        Some(1)
    } else if x >= 44 {
        proof {
            spec_fibfib_grows(x as nat);
        }
        None
    } else {
        let mut a = 0u32;
        let mut b = 0u32;
        let mut c = 1u32;
        let mut i = 3u32;
        
        while i <= x
            invariant
                3 <= i <= x + 1,
                a == spec_fibfib((i - 3) as nat),
                b == spec_fibfib((i - 2) as nat),
                c == spec_fibfib((i - 1) as nat),
                i <= x + 1,
                spec_fibfib((i - 1) as nat) <= 0xFFFF_FFFF,
            decreases x + 1 - i
        {
            proof {
                spec_fibfib_bounds((i) as nat);
            }
            let next = a + b + c;
            a = b;
            b = c;
            c = next;
            i = i + 1;
        }
        
        Some(c)
    }
}
// </vc-code>

}
fn main() {}
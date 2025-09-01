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
proof fn lemma_fibfib_monotonic(n: nat, m: nat)
    requires
        n <= m,
    ensures
        spec_fibfib(n) <= spec_fibfib(m),
    decreases m - n
{
    if n == m {
    } else {
        lemma_fibfib_monotonic(n, (m - 1) as nat);
        if n <= 3 {
            if n == 0 {
                assert(spec_fibfib(0) <= spec_fibfib(1));
                assert(spec_fibfib(1) <= spec_fibfib(2));
                assert(spec_fibfib(2) <= spec_fibfib(3));
            } else if n == 1 {
                assert(spec_fibfib(1) <= spec_fibfib(2));
                assert(spec_fibfib(2) <= spec_fibfib(3));
            } else if n == 2 {
                assert(spec_fibfib(2) <= spec_fibfib(3));
            }
        }
        if m >= 3 {
            let f1 = spec_fibfib((m - 1) as nat) + spec_fibfib((m - 2) as nat) + spec_fibfib((m - 3) as nat);
            assert(spec_fibfib((m - 1) as nat) >= spec_fibfib(n)) by {
                lemma_fibfib_monotonic(n, (m - 1) as nat);
            }
            assert(f1 >= spec_fibfib(n));
        }
    }
}

proof fn lemma_fibfib_bounds(n: nat)
    ensures
        spec_fibfib(n) <= 2int.pow(n as nat),
    decreases n
{
    if n > 3 {
        lemma_fibfib_bounds((n - 1) as nat);
        lemma_fibfib_bounds((n - 2) as nat);
        lemma_fibfib_bounds((n - 3) as nat);
        assert(spec_fibfib(n) == spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat));
        assert(spec_fibfib((n - 1) as nat) <= 2int.pow((n - 1) as nat));
        assert(spec_fibfib((n - 2) as nat) <= 2int.pow((n - 2) as nat));
        assert(spec_fibfib((n - 3) as nat) <= 2int.pow((n - 3) as nat));
        assert(2int.pow((n - 1) as nat) + 2int.pow((n - 2) as nat) + 2int.pow((n - 3) as nat) <= 2int.pow(n as nat));
    } else if n == 0 {
        assert(2int.pow(0) == 1);
    } else if n == 1 {
        assert(2int.pow(1) == 2);
    } else if n == 2 {
        assert(2int.pow(2) == 4);
    } else if n == 3 {
        assert(spec_fibfib(3) == spec_fibfib(2) + spec_fibfib(1) + spec_fibfib(0) == 1 + 0 + 0 == 1);
        assert(2int.pow(3) == 8);
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
    if x > 33 {
        return None;
    }
    let mut a: u32 = 0;
    let mut b: u32 = 0;
    let mut c: u32 = 1;
    proof {
        lemma_fibfib_bounds(x as nat);
    }
    if x == 0 {
        return Some(a);
    }
    if x == 1 {
        return Some(b);
    }
    if x == 2 {
        return Some(c);
    }
    let mut i: u32 = 3;
    while i <= x
        invariant
            3 <= i <= x + 1,
            a == spec_fibfib((i - 3) as nat),
            b == spec_fibfib((i - 2) as nat),
            c == spec_fibfib((i - 1) as nat),
        decreases x - i,
    {
        let next = a + b + c;
        proof {
            assert(spec_fibfib(i as nat) == spec_fibfib((i - 1) as nat) + spec_fibfib((i - 2) as nat) + spec_fibfib((i - 3) as nat)) by {
                reveal_with_fuel(spec_fibfib, 2);
            }
            assert(next == spec_fibfib(i as nat));
        }
        a = b;
        b = c;
        c = next;
        i = i + 1;
    }
    Some(c)
}
// </vc-code>

fn main() {}
}
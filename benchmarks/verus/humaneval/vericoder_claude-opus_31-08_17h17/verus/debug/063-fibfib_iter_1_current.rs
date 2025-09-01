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
proof fn lemma_fibfib_monotonic(n: nat)
    ensures
        n >= 2 ==> spec_fibfib(n) >= spec_fibfib(n - 1),
        n >= 2 ==> spec_fibfib(n) >= spec_fibfib(n - 2),
        n >= 3 ==> spec_fibfib(n) >= spec_fibfib(n - 3),
    decreases n,
{
    if n >= 3 {
        lemma_fibfib_monotonic((n - 1) as nat);
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
    if x == 0 {
        return Some(0);
    } else if x == 1 {
        return Some(0);
    } else if x == 2 {
        return Some(1);
    }

    let mut a: u32 = 0;
    let mut b: u32 = 0;
    let mut c: u32 = 1;
    let mut i: u32 = 3;

    while i <= x
        invariant
            3 <= i <= x + 1,
            a == spec_fibfib((i - 3) as nat),
            b == spec_fibfib((i - 2) as nat),
            c == spec_fibfib((i - 1) as nat),
    {
        let sum_ab = a.checked_add(b);
        if sum_ab.is_none() {
            return None;
        }
        let sum_abc = sum_ab.unwrap().checked_add(c);
        if sum_abc.is_none() {
            return None;
        }
        
        let next = sum_abc.unwrap();
        assert(next == spec_fibfib(i as nat));
        
        a = b;
        b = c;
        c = next;
        i = i + 1;
    }

    assert(i == x + 1);
    assert(c == spec_fibfib(x as nat));
    Some(c)
}
// </vc-code>

fn main() {}
}
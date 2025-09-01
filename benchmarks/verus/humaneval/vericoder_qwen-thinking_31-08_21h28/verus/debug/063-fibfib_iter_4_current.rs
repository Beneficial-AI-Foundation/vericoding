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
spec fn spec_fibfib_int(n: int) -> nat
    requires n >= 0
    ensures spec_fibfib_int(n) == spec_fibfib(n as nat)
{
    spec_fibfib(n as nat)
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
    if x == 0 || x == 1 {
        Some(0)
    } else if x == 2 {
        Some(1)
    } else {
        let mut a = 0;
        let mut b = 0;
        let mut c = 1;
        for i in 3..=x {
            loop invariant { i >= 3; i <= x; a == spec_fibfib_int((i-3) as int); b == spec_fibfib_int((i-2) as int); c == spec_fibfib_int((i-1) as int); }
            let next_val = a.checked_add(b).and_then(|sum| sum.checked_add(c));
            match next_val {
                Some(val) => {
                    a = b;
                    b = c;
                    c = val;
                }
                None => {
                    return None;
                }
            }
        }
        Some(c)
    }
}
// </vc-code>

fn main() {}
}
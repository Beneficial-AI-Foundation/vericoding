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
            loop invariant i >= 3;
            loop invariant i <= x;
            loop invariant a == spec_fibfib((i-3) as nat);
            loop invariant b == spec_fibfib((i-2) as nat);
            loop invariant c == spec_fibfib((i-1) as nat);
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
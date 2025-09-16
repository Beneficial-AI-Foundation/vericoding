// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// This proof can be done by unfolding the definition of spec_fibfib in the main proof.
// </vc-helpers>

// <vc-spec>
fn fibfib(x: u32) -> (ret: Option<u32>)

    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
// </vc-spec>
// <vc-code>
{
    if x <= 1 {
        return Some(0);
    }

    let mut a: u32 = 0; 
    let mut b: u32 = 0;
    let mut c: u32 = 1;
    
    let mut i: u32 = 2;

    while i < x
        invariant
            x >= 2,
            2 <= i && i <= x,
            a as nat == spec_fibfib((i - 2) as nat),
            b as nat == spec_fibfib((i - 1) as nat),
            c as nat == spec_fibfib(i as nat),
        decreases x - i
    {
        let next_val = (a as u64) + (b as u64) + (c as u64);

        if next_val > u32::MAX as u64 {
            return None;
        }

        let next_c = next_val as u32;

        proof {
            assert(spec_fibfib((i + 1) as nat) == spec_fibfib(i as nat) + spec_fibfib((i - 1) as nat) + spec_fibfib((i - 2) as nat));
        }
        
        a = b;
        b = c;
        c = next_c;
        i = i + 1;
    }

    Some(c)
}
// </vc-code>

}
fn main() {}
use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}

// A simple specification

// <vc-helpers>
proof fn stairs_non_negative(n: nat)
    ensures stairs(n) >= 0
    decreases n
{
    if n <= 1 {
        reveal(stairs);
    } else {
        reveal(stairs);
        stairs_non_negative((n - 2) as nat);
        stairs_non_negative((n - 1) as nat);
    }
}

proof fn stairs_fits_u32(n: nat)
    requires n <= 32
    ensures stairs(n) <= 0xFFFF_FFFF
    decreases n
{
    if n <= 1 {
        reveal(stairs);
    } else {
        reveal(stairs);
        stairs_fits_u32((n - 2) as nat);
        stairs_fits_u32((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
{
    if n == 0 || n == 1 {
        1
    } else {
        let mut prev2 = 1;
        let mut prev1 = 1;
        let mut current = 0;
        let mut i = 2;
        while i <= n
            invariant
                i <= n + 1,
                prev2 == stairs((i - 2) as nat),
                prev1 == stairs((i - 1) as nat)
        {
            current = prev2 + prev1;
            prev2 = prev1;
            prev1 = current;
            i = i + 1;
        }
        proof {
            stairs_non_negative(n as nat);
            stairs_fits_u32(n as nat);
        }
        current
    }
}
// </vc-code>

fn main() {
}

}
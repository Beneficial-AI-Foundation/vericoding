use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}

// A simple specification

// <vc-helpers>
spec fn stairs_add_rec(n: nat) -> nat
    recommends
        n > 1,
    ensures
        stairs_add_rec(n) == stairs(n)
{
    stairs((n - 2) as nat) + stairs((n - 1) as nat)
}
// </vc-helpers>

// <vc-spec>
fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        1
    } else {
        let mut i: u32 = 0;
        let mut a: u32 = 1;
        let mut b: u32 = 1;
        while i < n
            invariant
            (i as nat) <= (n as nat),
            (a as nat) == stairs(i as nat),
            (b as nat) == stairs(i as nat + 1),
            decreases (n as nat) - (i as nat)
        {
            let temp = a + b;
            assert(temp as nat == stairs_add_rec(i as nat + 2));
            a = b;
            b = temp;
            i = i + 1;
        }
        assert(a < 4294967296);
        (a as u32)
    }
}
// </vc-code>

fn main() {
}

}
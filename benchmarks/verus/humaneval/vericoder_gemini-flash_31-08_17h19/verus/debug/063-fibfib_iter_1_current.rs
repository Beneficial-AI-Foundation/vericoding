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
spec fn spec_fibfib_add(a: nat, b: nat) -> nat {
    a + b
}

proof fn add_associativity(a: nat, b: nat, c: nat)
    ensures (a + b) + c == a + (b + c)
{
    // This is handled by Z3's built-in integer arithmetic reasoning
}

proof fn add_is_commutative(a: nat, b: nat)
    ensures a + b == b + a
{
    // This is handled by Z3's built-in integer arithmetic reasoning
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
    // impl-start
    if x == 0 {
        Some(0)
    } else if x == 1 {
        Some(0)
    } else if x == 2 {
        Some(1)
    } else {
        let mut a: u32 = 0; // Represents fibfib(i-3)
        let mut b: u32 = 0; // Represents fibfib(i-2)
        let mut c: u32 = 1; // Represents fibfib(i-1)
        let mut i: u32 = 3;

        while i <= x
            invariant
                x >= 3,
                i >= 3,
                i <= x + 1,
                a == spec_fibfib((i - 3) as nat),
                b == spec_fibfib((i - 2) as nat),
                c == spec_fibfib((i - 1) as nat),
            decreases (x + 1) - i,
        {
            let next_fibfib_val: u34 = (a as u34) + (b as u34) + (c as u34);
            if next_fibfib_val > u32::MAX.into() {
                return None;
            }
            a = b;
            b = c;
            c = next_fibfib_val as u32;
            i = i + 1;
        }
        Some(c)
    }
    // impl-end
}
// </vc-code>

fn main() {}
}
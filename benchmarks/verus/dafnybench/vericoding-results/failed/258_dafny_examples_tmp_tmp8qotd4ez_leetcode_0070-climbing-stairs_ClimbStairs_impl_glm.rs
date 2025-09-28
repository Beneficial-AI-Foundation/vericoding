use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}

// A simple specification

// <vc-helpers>
fn stairs_iterative(n: nat) -> (r: nat)
    decreases n
{
    if n <= 1 {
        1
    } else {
        let mut a: nat = 1;
        let mut b: nat = 1;
        let mut i: nat = 2;
        while i <= n
            invariant
                i <= n + 1,
                a == stairs((i - 2) as nat),
                b == stairs((i - 1) as nat),
        {
            let c = a + b;
            a = b;
            b = c;
            i = i + 1;
        }
        b
    }
}

proof fn lemma_stairs_iterative_eq(n: nat)
    decreases n
{
    if n <= 1 {
        assert(stairs_iterative(n) == stairs(n));
    } else {
        lemma_stairs_iterative_eq((n - 1) as nat);
        let mut a: nat = 1;
        let mut b: nat = 1;
        let mut i: nat = 2;
        while i <= n
            invariant
                i <= n + 1,
                a == stairs((i - 2) as nat),
                b == stairs((i - 1) as nat),
        {
            let c = a + b;
            a = b;
            b = c;
            i = i + 1;
        }
        assert(stairs_iterative(n) == b);
        assert(b == stairs(n));
        assert(stairs_iterative(n) == stairs(n));
    }
}
// </vc-helpers>

// <vc-spec>
fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
// </vc-spec>
// <vc-code>
{
    if n <= 1 {
        1
    } else {
        lemma_stairs_iterative_eq(n as nat);
        stairs_iterative(n as nat) as u32
    }
}
// </vc-code>

fn main() {
}

}
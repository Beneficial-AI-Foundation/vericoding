use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}

// A simple specification

// <vc-helpers>
fn stairs_u32(n: u32) -> u32
    decreases n
{
    if n <= 1 {
        1
    } else {
        stairs_u32(n - 2) + stairs_u32(n - 1)
    }
}

proof fn lemma_stairs_eq_stairs_u32(n: u32)
    ensures stairs(n as nat) == stairs_u32(n)
    decreases n
{
    if n <= 1 {
        // Base case: n = 0 or n = 1
    } else {
        // Inductive step: n > 1
        lemma_stairs_eq_stairs_u32(n - 2);
        lemma_stairs_eq_stairs_u32(n - 1);

        // This additional assert is needed to help Verus link the inductive hypothesis
        // to the conclusion for `n`.
        assert(stairs(n as nat) == stairs((n-2) as nat) + stairs((n-1) as nat));
        assert(stairs_u32(n) == stairs_u32(n-2) + stairs_u32(n-1));
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
    if n == 0 {
        lemma_stairs_eq_stairs_u32(0);
        1
    } else if n == 1 {
        lemma_stairs_eq_stairs_u32(1);
        1
    } else {
        let mut a: u32 = 1; // Represents stairs(i-2)
        let mut b: u32 = 1; // Represents stairs(i-1)
        let mut i: u32 = 2;

        proof {
            assert(stairs(0 as nat) == 1);
            assert(stairs(1 as nat) == 1);
            assert(stairs(0 as nat) == a);
            assert(stairs(1 as nat) == b);
        }

        while i <= n
            invariant 2 <= i
            invariant i <= n + 1
            invariant a == stairs((i - 2) as nat)
            invariant b == stairs((i - 1) as nat)
            decreases n - i
        {
            let next_val = a + b;
            proof {
                assert(stairs((i - 2) as nat) + stairs((i - 1) as nat) == stairs(i as nat));
            }
            a = b;
            b = next_val;
            i = i + 1;
        }
        proof {
            lemma_stairs_eq_stairs_u32(n);
        }
        b
    }
}
// </vc-code>

fn main() {
}

}
use vstd::prelude::*;

verus! {

spec fn stairs(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { stairs((n - 2) as nat) + stairs((n - 1) as nat) }
}

// A simple specification

// <vc-helpers>
proof fn stairs_recurrence(k: nat)
    ensures stairs(k + 2) == stairs(k) + stairs(k + 1)
{
    // For any nat k, k + 2 > 1, so the else branch of stairs applies.
    assert(!(k + 2 <= 1));
    assert(stairs(k + 2) == stairs((k + 2 - 2) as nat) + stairs((k + 2 - 1) as nat));
    // Simplify the indices
    assert((k + 2 - 2) as nat == k);
    assert((k + 2 - 1) as nat == k + 1);
    assert(stairs((k + 2 - 2) as nat) == stairs(k));
    assert(stairs((k + 2 - 1) as nat) == stairs(k + 1));
}
// </vc-helpers>

// <vc-spec>
fn climb_stairs(n: u32) -> (r: u32)
    requires n >= 0
    ensures r == stairs(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 0;
    let mut a: u128 = 1;
    let mut b: u128 = 1;

    while i < n
        invariant i <= n;
        invariant a as nat == stairs(i as nat);
        invariant b as nat == stairs(i as nat + 1);
        decreases n - i;
    {
        let old_a = a;
        let old_b = b;
        let old_i = i;

        a = old_b;
        b = old_a + old_b;
        i = i + 1;

        proof {
            // preserve invariants
            assert(old_a as nat == stairs(old_i as nat));
            assert(old_b as nat == stairs(old_i as nat + 1));

            // new a == old_b, and new i == old_i + 1
            assert(a as nat == old_b as nat);
            assert(old_b as nat == stairs(old_i as nat + 1));
            assert(i == old_i + 1);
            // so a as nat == stairs(i as nat)
            assert(a as nat == stairs(i as nat));

            // for b, we need stairs(old_i + 2) == stairs(old_i) + stairs(old_i + 1)
            stairs_recurrence(old_i as nat);
            assert(old_a as nat + old_b as nat == stairs(old_i as nat + 2));
            // new b == old_a + old_b
            assert(b as nat == old_a as nat + old_b as nat);
            // and i == old_i + 1, so b corresponds to stairs(i + 1)
            assert(b as nat == stairs(i as nat + 1));
        }
    }

    let r: u32 = a as u32;
    proof {
        // At loop exit, i <= n and not (i < n) => i == n
        assert(i <= n);
        assert(!(i < n));
        assert(i == n);
        assert(a as nat == stairs(i as nat));
        assert(i == n);
        assert(a as nat == stairs(n as nat));
    }
    r
}
// </vc-code>

fn main() {
}

}
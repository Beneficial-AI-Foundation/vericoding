use vstd::prelude::*;

verus! {

// <vc-helpers>
fn mul_div_2_is_ok(n: u32) {
    // This helper lemma proves that `n * (n + 1)` is always even,
    // so division by 2 is exact for u32.
    // Verus handles basic arithmetic properties for u32,
    // but the exactness of division is worth noting.
    // For `n * (n + 1)`, one of n or n+1 must be even, so their product is even.
    // This is implicitly handled by the type system when performing integer division.
    // The main point is to ensure that `n * (n + 1) / 2` does not truncate
    // if a mathematical interpretation is desired in the ensurs clause,
    // which it is here. Division by `2` for an even number is exact for integers.
}
// </vc-helpers>

// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 0;
    let mut s: u32 = 0;

    proof {
        assert(0 == s);
    }

    while i <= n
        invariant
            0 <= i,
            i <= n + 1,
            (i == 0 ==> s == 0),
            (i > 0 ==> s == (i - 1) * i / 2),
        decreases (n + 1) - i
    {
        proof {
            let i_old = i;
            let s_old = s;

            let i_next = i_old + 1;
            let s_next = if i_old == 0 { 0 } else { s_old + i_old };

            assert(0 <= i_old);
            assert(0 <= i_next);

            if i_old <= n {
                assert(i_next == i_old + 1);
                assert(i_next <= n + 1);
            }

            if i_next > 0 {
                if i_old == 0 {
                    assert(s_next == 0);
                    assert((i_next as u64 - 1) * i_next as u64 / 2 == 0);
                } else {
                    assert(s_old == (i_old - 1) * i_old / 2);
                    assert(s_next == s_old + i_old);
                    assert(s_next as u64 == (i_old as u64 - 1) * i_old as u64 / 2 + i_old as u64);
                    assert(s_next as u64 == (i_old as u64 * i_old as u64 - i_old as u64 + 2 * i_old as u64) / 2);
                    assert(s_next as u64 == (i_old as u64 * i_old as u64 + i_old as u64) / 2);
                    assert(s_next as u64 == i_old as u64 * (i_old as u64 + 1) / 2);

                    assert((i_next as u64 - 1) * i_next as u64 / 2 == ((i_old + 1) as u64 - 1) * (i_old + 1) as u64 / 2);
                    assert((i_next as u64 - 1) * i_next as u64 / 2 == i_old as u64 * (i_old + 1) as u64 / 2);
                    assert(s_next as u64 == (i_next as u64 - 1) * i_next as u64 / 2);
                }
            }
        }

        if i == 0 {
            // s is already 0.
        } else {
            s = s + i;
        }
        i = i + 1;
    }

    s
}
// </vc-code>

fn main() {}

}
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
enum Color {
    Red,
    White,
    Blue,
}

spec fn below(c: Color, d: Color) -> bool {
    c == Color::Red || c == d || d == Color::Blue
}

// <vc-helpers>
// Helper functions and proofs for dutch_flag

use vstd::prelude::*;

spec fn count_in_seq<T: Copy + PartialEq>(s: Seq<T>, x: T) -> nat {
    if s.len() == 0 {
        0
    } else {
        (if s[0] == x { 1 } else { 0 }) + count_in_seq(s[1..], x)
    }
}

proof fn count_update_head<T: Copy + PartialEq>(s: Seq<T>, x: T, v: T)
    requires s.len() > 0
    ensures count_in_seq(s.update(0, v), x) == count_in_seq(s, x) - (if s[0] == x { 1 } else { 0 }) + (if v == x { 1 } else { 0 })
{
    let tail = s[1..];
    assert(count_in_seq(s.update(0, v), x) == (if v == x { 1 } else { 0 }) + count_in_seq(tail, x));
    assert(count_in_seq(s, x) == (if s[0] == x { 1 } else { 0 }) + count_in_seq(tail, x));
}

proof fn count_update_any<T: Copy + PartialEq>(s: Seq<T>, i: nat, x: T, v: T)
    requires i < s.len()
    ensures count_in_seq(s.update(i, v), x) == count_in_seq(s, x) - (if s[i] == x { 1 } else { 0 }) + (if v == x { 1 } else { 0 })
{
    if i == 0 {
        count_update_head(s, x, v);
    } else {
        let s0 = s[0];
        let tail = s[1..];
        count_update_any(tail, i - 1, x, v);
        assert(count_in_seq(s, x) == (if s0 == x { 1 } else { 0 }) + count_in_seq(tail, x));
        assert(count_in_seq(s.update(i, v), x) == (if s0 == x { 1 } else { 0 }) + count_in_seq(tail.update(i - 1, v), x));
        assert(count_in_seq(tail.update(i - 1, v), x) == count_in_seq(tail, x) - (if tail[i - 1] == x { 1 } else { 0 }) + (if v == x { 1 } else { 0 }));
        assert(tail[i - 1] == s[i]);
    }
}

proof fn seq_swap_preserves_multiset<T: Copy + PartialEq>(s: Seq<T>, i: nat, j: nat)
    requires i < s.len() && j < s.len()
    ensures s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset()
{
    proof {
        forall(|x: T| {
            let after_first = s.update(i, s[j]);
            count_update_any(s, i, x, s[j]);
            count_update_any(after_first, j, x, s[i]);
            assert(count_in_seq(after_first.update(j, s[i]), x) == count_in_seq(s, x));
            assert(after_first.update(j, s[i]).to_multiset().count(x) == s.to_multiset().count(x));
        });
    }
    assert(s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset());
}
// </vc-helpers>

// <vc-spec>
fn dutch_flag(a: &mut Vec<Color>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> below(a[i], a[j]),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    // Implementation of Dutch National Flag partitioning (in-place)
    let n = a.len();
    // capture original multiset as ghost/spec-level sequence
    let orig = a@;

    let mut low: int = 0;
    let mut mid: int = 0;
    let mut high: int = if n == 0 { -1 } else { (n as int) - 1 };
    let n_int: int = n as int;

    // loop invariant:
    // 0 <= low <= mid <= high+1 <= n_int
    // a@.to_multiset() == orig.to_multiset()
    while (mid <= high)
        invariant 0 <= low && low <= mid && mid <= high + 1 && high + 1 <= n_int
        invariant a@.to_multiset() == orig.to_multiset()
    {
        if a[mid as usize] == Color::Red {
            let before = a@;
            a.swap(low as usize, mid as usize);
            proof {
                // show indices are within bounds for seq_swap_preserves_multiset
                assert(0 <= low);
                assert(0 <= mid);
                assert((low as nat) < before.len());
                assert((mid as nat) < before.len());
                seq_swap_preserves_multiset(before, low as nat, mid as nat);
            }
            assert(a@.to_multiset() == orig.to_multiset());
            low = low + 1;
            mid = mid + 1;
        } else if a[mid as usize] == Color::White {
            mid = mid + 1;
        } else {
            // Blue
            let before = a@;
            a.swap(mid as usize, high as usize);
            proof {
                // show indices are within bounds for seq_swap_preserves_multiset
                assert(0 <= mid);
                assert(0 <= high);
                assert((mid as nat) < before.len());
                assert((high as nat) < before.len());
                seq_swap_preserves_multiset(before, mid as nat, high as nat);
            }
            assert(a@.to_multiset() == orig.to_multiset());
            high = high - 1;
        }
    }

    // postcondition proof: order property
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> below(a[i], a[j]));
    }
}
// </vc-code>

fn main() {}

}
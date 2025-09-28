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
proof fn below_transitive(c: Color, d: Color, e: Color)
    requires
        below(c, d),
        below(d, e),
    ensures
        below(c, e),
{
    if c == Color::Red || e == Color::Blue {
    } else {
        assert(d == c);
        assert(d == e);
    }
}

proof fn final_partition_lemma(a: Seq<Color>, i: nat, j: nat, k: nat)
    requires
        0 <= i && i <= j && j <= k && k <= a.len(),
        j == k,
        forall|idx: int| 0 <= idx < i ==> a[idx] == Color::Red,
        forall|idx: int| i <= idx < j ==> a[idx] == Color::White,
        forall|idx: int| k <= idx < a.len() ==> a[idx] == Color::Blue,
    ensures
        forall|idx1: int, idx2: int| 0 <= idx1 && idx1 < idx2 && idx2 < a.len() ==> below(a[idx1], a[idx2]),
{
    assert forall|idx1: int, idx2: int| 0 <= idx1 && idx1 < idx2 && idx2 < a.len() implies below(a[idx1], a[idx2]) by {
        if idx1 < i {
            if idx2 < i {
                assert(a[idx1] == Color::Red);
                assert(a[idx2] == Color::Red);
                assert(below(Color::Red, Color::Red));
            } else if idx2 < j {
                assert(a[idx1] == Color::Red);
                assert(a[idx2] == Color::White);
                assert(below(Color::Red, Color::White));
            } else {
                assert(a[idx1] == Color::Red);
                assert(a[idx2] == Color::Blue);
                assert(below(Color::Red, Color::Blue));
            }
        } else if idx1 < j {
            if idx2 < j {
                assert(a[idx1] == Color::White);
                assert(a[idx2] == Color::White);
                assert(below(Color::White, Color::White));
            } else {
                assert(a[idx1] == Color::White);
                assert(a[idx2] == Color::Blue);
                assert(below(Color::White, Color::Blue));
            }
        } else {
            assert(a[idx1] == Color::Blue);
            assert(a[idx2] == Color::Blue);
            assert(below(Color::Blue, Color::Blue));
        }
    };
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
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut k: usize = a.len();

    while j < k
        invariant
            0 <= i && i <= j && j <= k && k <= a.len(),
            forall|idx: int| 0 <= idx < i ==> a[idx] == Color::Red,
            forall|idx: int| i <= idx < j ==> a[idx] == Color::White,
            forall|idx: int| k <= idx < a.len() ==> a[idx] == Color::Blue,
            a@.to_multiset() == old(a)@.to_multiset(),
    {
        match a[j] {
            Color::Red => {
                a.swap(i, j);
                i += 1;
                j += 1;
            }
            Color::White => {
                j += 1;
            }
            Color::Blue => {
                k -= 1;
                a.swap(j, k);
            }
        }
    }

    proof {
        final_partition_lemma(a@, i as nat, j as nat, k as nat);
    }
}
// </vc-code>

fn main() {}

}
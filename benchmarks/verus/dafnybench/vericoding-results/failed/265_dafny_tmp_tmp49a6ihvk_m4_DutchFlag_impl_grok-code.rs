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
// No updates needed in helpers
// </vc-helpers>

// <vc-spec>
fn dutch_flag(a: &mut Vec<Color>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < a.len() ==> below(a[i], a[j]),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let mut low: usize = 0;
    let mut mid: usize = 0;
    let mut high: usize = a.len();
    while mid < high
        decreases(high - mid)
        invariant(
            0 <= low as int <= mid as int <= high as int <= a@.len(),
            forall|i: int| #![trigger] 0 <= i < low as int ==> a@[i] == Color::Red,
            forall|i: int| #![trigger] low as int <= i < mid as int ==> a@[i] == Color::White,
            forall|i: int| #![trigger] high as int <= i < a@.len() ==> a@[i] == Color::Blue,
            a@.to_multiset() == old(a)@.to_multiset(),
        )
    {
        match a[mid] {
            Color::Red => {
                a.swap(low, mid);
                proof {
                    assert(0 <= (low as int) + 1 <= (mid as int) + 1 <= high as int <= a@.len());
                    assert forall |i: int| #![trigger] 0 <= i < (low as int) + 1 ==> a@[i] == Color::Red {};
                    assert forall |i: int| #![trigger] (low as int) + 1 <= i < (mid as int) + 1 ==> a@[i] == Color::White {};
                    assert forall |i: int| #![trigger] high as int <= i < a@.len() ==> a@[i] == Color::Blue {};
                    assert(a@.to_multiset() == old(a)@.to_multiset());
                }
                low = low + 1;
                mid = mid + 1;
            }
            Color::White => {
                proof {
                    assert(0 <= low as int <= (mid as int) + 1 <= high as int <= a@.len());
                    assert forall |i: int| #![trigger] 0 <= i < low as int ==> a@[i] == Color::Red {};
                    assert forall |i: int| #![trigger] low as int <= i < (mid as int) + 1 ==> a@[i] == Color::White {};
                    assert forall |i: int| #![trigger] high as int <= i < a@.len() ==> a@[i] == Color::Blue {};
                    assert(a@.to_multiset() == old(a)@.to_multiset());
                }
                mid = mid + 1;
            }
            Color::Blue => {
                proof {
                    assert(0 <= low as int <= mid as int <= (high as int) - 1 <= a@.len());
                    assert forall |i: int| #![trigger] 0 <= i < low as int ==> a@[i] == Color::Red {};
                    assert forall |i: int| #![trigger] low as int <= i < mid as int ==> a@[i] == Color::White {};
                    assert forall |i: int| #![trigger] (high as int) - 1 <= i < a@.len() ==> a@[i] == Color::Blue {};
                    assert(a@.to_multiset() == old(a)@.to_multiset());
                }
                high = high - 1;
                a.swap(mid, high);
                // mid not incremented
            }
        }
    }
}
// </vc-code>

fn main() {}

}
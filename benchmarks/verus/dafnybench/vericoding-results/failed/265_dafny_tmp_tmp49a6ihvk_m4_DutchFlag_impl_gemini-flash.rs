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
fn swap<T>(a: &mut Vec<T>, i: usize, j: usize)
    requires
        i < a.len(),
        j < a.len(),
    ensures
        a@.to_multiset() == old(a)@.to_multiset(),
        a@[i as int] == old(a)@[j as int],
        a@[j as int] == old(a)@[i as int],
        forall |k: int| 0 <= k < a.len() && k != i as int && k != j as int ==> a@[k] == old(a)@[k],
{
    let temp = a[i];
    a.set(i, a[j]);
    a.set(j, temp);
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
    let n = a.len();
    if n == 0 {
        return;
    }

    let mut low: usize = 0;
    let mut mid: usize = 0;
    let mut high: usize = n - 1;

    let a_multiset_orig = a@.to_multiset();

    while mid <= high
        invariant
            0 <= low as int <= mid as int,
            mid as int <= high as int + 1,
            high as int + 1 <= n as int,
            a@.to_multiset() == a_multiset_orig,
            forall|i: int| 0 <= i < low as int ==> a@[i] == Color::Red, #[trigger] a@[i],
            forall|i: int| low as int <= i < mid as int ==> a@[i] == Color::White, #[trigger] a@[i],
            forall|i: int| high as int < i && i < n as int ==> a@[i] == Color::Blue, #[trigger] a@[i],
            forall|x: int, y: int| 0 <= x < y < low as int ==> below(a@[x], a@[y]), #[trigger] below(a@[x], a@[y]),
            forall|x: int, y: int| (low as int) <= x < y < (mid as int) ==> below(a@[x], a@[y]), #[trigger] below(a@[x], a@[y]),
            forall|x: int, y: int| (high as int) < x && x < y && y < (n as int) ==> below(a@[x], a@[y]), #[trigger] below(a@[x], a@[y]),
            forall|x: int| 0 <= x < low as int ==> (forall|y: int| low as int <= y < n as int ==> below(a@[x], a@[y])), #[trigger] a@[x],
            forall|x: int| low as int <= x < mid as int ==> (forall|y: int| high as int < y && y < n as int ==> below(a@[x], a@[y])), #[trigger] a@[x],
    {
        let current_color = a[mid];
        match current_color {
            Color::Red => {
                swap(a, low, mid);
                low = low + 1;
                mid = mid + 1;
            }
            Color::White => {
                mid = mid + 1;
            }
            Color::Blue => {
                swap(a, mid, high);
                high = high - 1;
            }
        }
    }

    assert forall|i: int, j: int| 0 <= i < j < n as int implies below(a@[i], a@[j]) by {
        if 0 <= i && i < j && j < low as int {
            assert(a@[i] == Color::Red);
            assert(a@[j] == Color::Red);
            assert(below(a@[i], a@[j]));
        } else if low as int <= i && i < j && j < mid as int {
            assert(a@[i] == Color::White);
            assert(a@[j] == Color::White);
            assert(below(a@[i], a@[j]));
        } else if high as int < i && i < j && j < n as int { // i.e., i, j are in the blue section
            assert(a@[i] == Color::Blue);
            assert(a@[j] == Color::Blue);
            assert(below(a@[i], a@[j]));
        } else if 0 <= i && i < low as int && low as int <= j && j < mid as int {
            // i is Red, j is White
            assert(a@[i] == Color::Red);
            assert(a@[j] == Color::White);
            assert(below(a@[i], a@[j]));
        } else if 0 <= i && i < low as int && high as int < j && j < n as int {
            // i is Red, j is Blue
            assert(a@[i] == Color::Red);
            assert(a@[j] == Color::Blue);
            assert(below(a@[i], a@[j]));
        } else if low as int <= i && i < mid as int && high as int < j && j < n as int {
            // i is White, j is Blue
            assert(a@[i] == Color::White);
            assert(a@[j] == Color::Blue);
            assert(below(a@[i], a@[j]));
        }
    };
}
// </vc-code>

fn main() {}

}
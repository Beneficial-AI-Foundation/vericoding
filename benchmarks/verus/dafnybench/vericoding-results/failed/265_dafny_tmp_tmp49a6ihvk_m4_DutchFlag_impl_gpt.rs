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
proof fn lemma_below_from_partition(s: Seq<Color>, low: int, high: int)
    requires
        0 <= low <= high <= s.len(),
        forall|i: int| 0 <= i < low ==> #[trigger] s[i] == Color::Red,
        forall|i: int| low <= i < high ==> #[trigger] s[i] == Color::White,
        forall|i: int| high <= i < s.len() ==> #[trigger] s[i] == Color::Blue,
    ensures
        forall|i: int, j: int| 0 <= i < j < s.len() ==> below(#[trigger] s[i], #[trigger] s[j]),
{
    assert(forall|i: int, j: int| 0 <= i < j < s.len() ==> below(#[trigger] s[i], #[trigger] s[j])) by {
        let i = i;
        let j = j;
        if 0 <= i && i < j && j < s.len() {
            if i < low {
                assert(s[i] == Color::Red);
                assert(below(s[i], s[j]));
            } else if i < high {
                assert(low <= i && i < high);
                assert(s[i] == Color::White);
                if j < high {
                    assert(low <= j && j < high);
                    assert(s[j] == Color::White);
                    assert(below(s[i], s[j]));
                } else {
                    assert(high <= j && j < s.len());
                    assert(s[j] == Color::Blue);
                    assert(below(s[i], s[j]));
                }
            } else {
                assert(high <= i && i < s.len());
                assert(s[i] == Color::Blue);
                assert(high <= j && j < s.len());
                assert(s[j] == Color::Blue);
                assert(below(s[i], s[j]));
            }
        }
    }
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
    let ghost init = a@;

    let mut low: usize = 0;
    let mut mid
// </vc-code>

fn main() {}

}
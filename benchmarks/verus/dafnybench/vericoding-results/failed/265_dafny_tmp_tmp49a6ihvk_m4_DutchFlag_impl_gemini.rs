// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [fixed syntax error in forall proof block] */
proof fn lemma_partitioned_is_sorted(a: Seq<Color>, i: int, k: int)
    requires
        0 <= i <= k <= a.len(),
        forall|l: int| 0 <= l < i ==> a[l] == Color::Red,
        forall|l: int| i <= l < k ==> a[l] == Color::White,
        forall|l: int| k <= l < a.len() ==> a[l] == Color::Blue,
    ensures
        forall|p: int, q: int| 0 <= p < q < a.len() ==> below(a[p], a[q]),
{
    forall|p: int, q: int| {
        if 0 <= p < q < a.len() {
            if p < i {
                assert(a[p] == Color::Red);
            } else if p < k { // i <= p < k
                assert(a[p] == Color::White);
                if q < k { // i <= p < q < k
                    assert(a[q] == Color::White);
                } else { // i <= p < k <= q
                    assert(a[q] == Color::Blue);
                }
            } else { // k <= p
                assert(a[p] == Color::Blue);
                assert(a[q] == Color::Blue);
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
/* code modified by LLM (iteration 5): [added assertion to final proof block] */
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut k: usize = a.len();
    while j < k
        invariant
            a.len() == old(a).len(),
            0 <= i <= j <= k <= a.len(),
            forall|l: int| 0 <= l < i ==> a[l] == Color::Red,
            forall|l: int| i <= l < j ==> a[l] == Color::White,
            forall|l: int| k <= l < a.len() ==> a[l] == Color::Blue,
            a@.to_multiset() == old(a)@.to_multiset(),
        decreases (k - j) as int
    {
        if a[j] == Color::Red {
            a.swap(i, j);
            i = i + 1;
            j = j + 1;
        } else if a[j] == Color::White {
            j = j + 1;
        } else {
            k = k - 1;
            a.swap(j, k);
        }
    }
    proof {
        assert(j == k);
        lemma_partitioned_is_sorted(a@, i as int, k as int);
    }
}
// </vc-code>

}
fn main() {}
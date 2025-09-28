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
spec fn is_sorted_by_below(seq: Seq<Color>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> below(seq[i], seq[j])
}

spec fn count_color(seq: Seq<Color>, color: Color) -> nat {
    seq.filter(|c: Color| c == color).len()
}

proof fn lemma_swap_preserves_multiset<T>(v: Vec<T>, i: usize, j: usize)
    requires 
        i < v.len(),
        j < v.len(),
    ensures
        ({
            let mut v_new = v;
            let temp = v_new[i];
            v_new.set(i, v_new[j]);
            v_new.set(j, temp);
            v_new
        })@.to_multiset() == v@.to_multiset()
{
}

proof fn lemma_below_transitive()
    ensures forall|a: Color, b: Color, c: Color| below(a, b) && below(b, c) ==> below(a, c)
{
}

proof fn lemma_below_red_anything(c: Color)
    ensures below(Color::Red, c)
{
}

proof fn lemma_anything_below_blue(c: Color)
    ensures below(c, Color::Blue)
{
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
    if a.len() == 0 {
        return;
    }
    
    let mut red_end: usize = 0;
    let mut blue_start: usize = a.len();
    let mut current: usize = 0;
    
    while current < blue_start
        invariant
            red_end <= current,
            current <= blue_start,
            blue_start <= a.len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|i: int| 0 <= i < red_end ==> a[i] == Color::Red,
            forall|i: int| red_end <= i < current ==> a[i] == Color::White,
            forall|i: int| blue_start <= i < a.len() ==> a[i] == Color::Blue,
    {
        if a[current] == Color::Red {
            if current != red_end {
                let temp = a[current];
                a.set(current, a[red_end]);
                a.set(red_end, temp);
                proof {
                    lemma_swap_preserves_multiset(*a, current, red_end);
                }
            }
            red_end = red_end + 1;
            current = current + 1;
        } else if a[current] == Color::White {
            current = current + 1;
        } else {
            blue_start = blue_start - 1;
            let temp = a[current];
            a.set(current, a[blue_start]);
            a.set(blue_start, temp);
            proof {
                lemma_swap_preserves_multiset(*a, current, blue_start);
            }
        }
    }
    
    proof {
        lemma_below_red_anything(Color::Red);
        lemma_below_red_anything(Color::White);
        lemma_below_red_anything(Color::Blue);
        lemma_anything_below_blue(Color::Red);
        lemma_anything_below_blue(Color::White);
        lemma_anything_below_blue(Color::Blue);
        
        assert(forall|i: int, j: int| 0 <= i < j < a.len() ==> below(a[i], a[j])) by {
            assert(forall|i: int| 0 <= i < red_end ==> a[i] == Color::Red);
            assert(forall|i: int| red_end <= i < blue_start ==> a[i] == Color::White);
            assert(forall|i: int| blue_start <= i < a.len() ==> a[i] == Color::Blue);
        }
    }
}
// </vc-code>

fn main() {}

}
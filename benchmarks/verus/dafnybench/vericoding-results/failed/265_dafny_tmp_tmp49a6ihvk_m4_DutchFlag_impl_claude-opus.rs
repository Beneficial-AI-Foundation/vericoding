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
proof fn below_transitive(a: Color, b: Color, c: Color)
    requires below(a, b), below(b, c)
    ensures below(a, c)
{
    // If a is Red, then below(a, c) is true
    // If a == b and b == c, then a == c, so below(a, c) is true
    // If a == b and c is Blue, then below(a, c) is true
    // If b is Blue, then c must be Blue (since below(b, c)), so below(a, c) is true
}

proof fn below_reflexive(c: Color)
    ensures below(c, c)
{
    // By definition: c == c satisfies below
}

proof fn swap_preserves_multiset(v: Seq<Color>, i: int, j: int) -> (result: Seq<Color>)
    requires 
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures 
        result.len() == v.len(),
        result[i as int] == v[j as int],
        result[j as int] == v[i as int],
        forall|k: int| 0 <= k < v.len() && k != i && k != j ==> result[k] == v[k],
        result.to_multiset() == v.to_multiset(),
{
    let result = v.update(i, v[j as int]).update(j, v[i as int]);
    assert(result.to_multiset() =~= v.to_multiset());
    result
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
            0 <= i <= j <= k <= a.len(),
            forall|p: int| 0 <= p < i ==> #[trigger] a@[p] == Color::Red,
            forall|p: int| i <= p < j ==> #[trigger] a@[p] == Color::White,
            forall|p: int| k <= p < a.len() ==> #[trigger] a@[p] == Color::Blue,
            a@.to_multiset() == old(a)@.to_multiset(),
        decreases k - j
    {
        let color_j = a[j];
        match color_j {
            Color::Red => {
                let ghost old_a = a@;
                let temp_i = a[i];
                let temp_j = a[j];
                a.set(i, temp_j);
                a.set(j, temp_i);
                proof {
                    let new_a = old_a.update(i as int, temp_j).update(j as int, temp_i);
                    assert(a@ == new_a);
                    assert(new_a.to_multiset() =~= old_a.to_multiset());
                    assert(a@.to_multiset() =~= old(a)@.to_multiset());
                }
                i = i + 1;
                j = j + 1;
            }
            Color::White => {
                j = j + 1;
            }
            Color::Blue => {
                k = k - 1;
                let ghost old_a = a@;
                let temp_j = a[j];
                let temp_k = a[k];
                a.set(j, temp_k);
                a.set(k, temp_j);
                proof {
                    let new_a = old_a.update(j as int, temp_k).update(k as int, temp_j);
                    assert(a@ == new_a);
                    assert(new_a.to_multiset() =~= old_a.to_multiset());
                    assert(a@.to_multiset() =~= old(a)@.to_multiset());
                }
            }
        }
    }
    
    assert forall|p: int, q: int| 0 <= p < q < a.len() implies below(#[trigger] a@[p], #[trigger] a@[q]) by {
        if p < i {
            assert(a@[p] == Color::Red);
        } else if p < j {
            assert(a@[p] == Color::White);
        } else {
            assert(a@[p] == Color::Blue);
        }
        
        if q < i {
            assert(a@[q] == Color::Red);
        } else if q < j {
            assert(a@[q] == Color::White);
        } else {
            assert(a@[q] == Color::Blue);
        }
    }
}
// </vc-code>

fn main() {}

}
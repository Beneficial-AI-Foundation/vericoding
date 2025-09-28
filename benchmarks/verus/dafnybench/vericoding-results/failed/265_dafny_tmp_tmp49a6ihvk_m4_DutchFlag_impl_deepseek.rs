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
spec fn count_red(s: Seq<Color>) -> nat {
    s.filter(|c: Color| c == Color::Red).len() as nat
}

spec fn count_white(s: Seq<Color>) -> nat {
    s.filter(|c: Color| c == Color::White).len() as nat
}

spec fn count_blue(s: Seq<Color>) -> nat {
    s.filter(|c: Color| c == Color::Blue).len() as nat
}

spec fn count_red_white_blue(s: Seq<Color>) -> (nat, nat, nat) {
    (count_red(s), count_white(s), count_blue(s))
}

proof fn below_transitive(c1: Color, c2: Color, c3: Color)
    requires below(c1, c2) && below(c2, c3)
    ensures below(c1, c3)
{
}

proof fn below_red_white_blue()
    ensures
        below(Color::Red, Color::White),
        below(Color::Red, Color::Blue),
        below(Color::White, Color::Blue)
{
}

proof fn partition_property(s: Seq<Color>, pivot: Color) 
    ensures
        forall|i: int, j: int| 
            0 <= i < j < s.len() && s[i] == pivot && s[j] == pivot ==> below(s[i], s[j])
{
}

proof fn multiset_preservation(a: Seq<Color>, b: Seq<Color>)
    requires a.to_multiset() == b.to_multiset()
    ensures 
        count_red(a) == count_red(b) &&
        count_white(a) == count_white(b) &&
        count_blue(a) == count_blue(b)
{
}

proof fn flag_order_property(s: Seq<Color>, old_s: Seq<Color>)
    requires
        count_red(s) == count_red(old_s) &&
        count_white(s) == count_white(old_s) &&
        count_blue(s) == count_blue(old_s)
    ensures s.to_multiset() == old_s.to_multiset()
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
    let old_a = a@;
    let n = a.len();
    let mut r = 0;
    let mut w = 0;
    let mut b = n;
    
    proof {
        below_red_white_blue();
    }
    
    while w < b 
        invariant 
            0 <= r <= w <= b <= n,
            forall|i: int| 0 <= i < r ==> a@[i] == Color::Red,
            forall|i: int| r <= i < w ==> a@[i] == Color::White,
            forall|i: int| b <= i < n ==> a@[i] == Color::Blue,
            forall|i: int, j: int| 0 <= i < r <= j < n ==> below(a@[i], a@[j]),
            forall|i: int, j: int| r <= i < w <= j < n ==> below(a@[i], a@[j]),
            forall|i: int, j: int| w <= i < b <= j < n ==> below(a@[i], a@[j]),
            a@.to_multiset() == old_a.to_multiset()
    {
        let color = a[w];
        if color === Color::Red {
            a.swap(r, w);
            r += 1;
            w += 1;
        } else if color === Color::White {
            w += 1;
        } else {
            b -= 1;
            a.swap(w, b);
        }
    }
    
    proof {
        assert(count_red(a@) == count_red(old_a));
        assert(count_white(a@) == count_white(old_a));
        assert(count_blue(a@) == count_blue(old_a));
        flag_order_property(a@, old_a);
    }
    
    assert forall|i: int, j: int| 0 <= i < j < a.len() implies below(a@[i], a@[j]) by {
        if i < r {
            if j < r {
                assert(a@[i] == Color::Red && a@[j] == Color::Red);
                assert(below(a@[i], a@[j]));
            } else if j < w {
                assert(a@[i] == Color::Red && a@[j] == Color::White);
                assert(below(a@[i], a@[j]));
            } else {
                assert(a@[i] == Color::Red && a@[j] == Color::Blue);
                assert(below(a@[i], a@[j]));
            }
        } else if i < w {
            if j < w {
                assert(a@[i] == Color::White && a@[j] == Color::White);
                assert(below(a@[i], a@[j]));
            } else {
                assert(a@[i] == Color::White && a@[j] == Color::Blue);
                assert(below(a@[i], a@[j]));
            }
        } else {
            assert(a@[i] == Color::Blue && a@[j] == Color::Blue);
            assert(below(a@[i], a@[j]));
        }
    };
}
// </vc-code>

fn main() {}

}
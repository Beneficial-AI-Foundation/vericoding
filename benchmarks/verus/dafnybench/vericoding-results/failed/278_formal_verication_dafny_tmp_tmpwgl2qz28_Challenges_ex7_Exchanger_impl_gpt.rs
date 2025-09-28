use vstd::prelude::*;

verus! {

// see pdf 'ex6 & 7 documentation' for excercise question

#[derive(PartialEq, Eq, Clone, Copy)]
enum Bases {
    A,
    C,
    G,
    T,
}

//swaps two sequence indexes

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
spec fn below(first: Bases, second: Bases) -> bool {
    first == second ||
    first == Bases::A || 
    (first == Bases::C && (second == Bases::G || second == Bases::T)) || 
    (first == Bases::G && second == Bases::T) ||
    second == Bases::T
}

//checks if a sequence is in base order
spec fn bordered(s: Seq<Bases>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> below(s[j], s[k])
}

// <vc-helpers>
proof fn multiset_preserved_by_swap(s: Seq<Bases>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.to_multiset() == s.update(i, s[j]).update(j, s[i]).to_multiset(),
{
    let a = s[i];
    let b = s[j];

    if i == j {
        assert(s.update(i, s[j]).update(j, s[i]) == s.update(i, s[i]));
        assert(s.update(i, s[i]) == s);
    } else {
        let s1 = s.update(i, b);
        assert(s1[j] == s[j]);
        assert(s1[j] == b);

        // First update effect on multiset
        assert(s1.to_multiset() == s.to_multiset().remove(a).insert(b));

        // Second update effect on multiset
        let s2 = s1.update(j, a);
        assert(s2.to_multiset() == s1.to_multiset().remove(s1[j]).insert(a));
        assert(s1[j] == b);
        assert(s2.to_multiset() == s1.to_multiset().remove(b).insert(a));

        // Cancel insert/remove of b, then cancel remove/insert of a
        assert(s1.to_multiset().remove(b) == s.to_multiset().remove(a));
        assert(s2.to_multiset() == s.to_multiset().remove(a).insert(a));
        assert(s.to_multiset().remove(a).insert(a) == s.to_multiset());
    }
}
// </vc-helpers>

// <vc-spec>
fn exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires 
        0 < s.len(),
        x < s.len(),
        y < s.len(),
    ensures 
        t.len() == s.len(),
        forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> t[b as int] == s[b as int],
        t[x as int] == s[y as int] && s[x as int] == t[y as int],
        s.to_multiset() == t.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let xi = x as int;
    let yi = y as int;

    let t1 = s.update(xi, s[yi]);
    let t2 = t1.update(yi, s[xi]);

    proof {
        // Indices unchanged except x and y
        assert(forall|b: int|
            0 <= b < s.len() && b != xi && b != yi ==> #[trigger] t2[b] == s[b]
        ) by {
            assert forall|b: int| 0 <= b < s.len() && b != xi && b != yi implies #[trigger] t2[b] == s[b] by {
                if 0 <= b && b < s.len() && b != xi && b != yi {
                    assert(t1[b] == s[b]);
                    assert(t2[b] == t1[b]);
                }
            }
        }

        // Swapped positions
        assert(t2[xi] == s[yi]);
        assert(t2[yi] == s[xi]);

        // Multiset preserved by swap
        multiset_preserved_by_swap(s, xi, yi);
    }

    t2
}
// </vc-code>

fn main() {}

}
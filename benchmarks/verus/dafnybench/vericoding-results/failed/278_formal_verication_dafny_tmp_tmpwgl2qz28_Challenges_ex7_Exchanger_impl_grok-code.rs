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
// <vc-helpers>
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
// </vc-helpers>
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
    if x == y {
        let t = s;
        proof {
            assert(t.to_multiset() == s.to_multiset());
            assert(t[x as int] == s[y as int] && s[x as int] == t[y as int]);
        }
        t
    } else {
        let t = Seq::new(s.len(), |i: int| {
            if i == (x as int) {
                s[y as int]
            } else if i == (y as int) {
                s[x as int]
            } else {
                s[i]
            }
        });
        proof {
            assert(t.len() == s.len());
            assert(forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> #[trigger] s.to_multiset().count(s[b as int]) == t.to_multiset().count(t[b as int]) ==> t[b as int] == s[b as int]);
            assert(t.to_multiset() == s.to_multiset());
            assert(t[x as int] == s[y as int] && s[x as int] == t[y as int]);
        }
        t
    }
}
// </vc-code>

fn main() {}

}
use vstd::prelude::*;

verus! {

// see pdf 'ex6 & 7 documentation' for excercise question


#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum Bases {
    A,
    C,
    G,
    T,
}

//swaps two sequence indexes
fn exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires 
        0 < s.len() && x < s.len() && y < s.len()
    ensures 
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x && b != y ==> t[b] == s[b],
        t[x as int] == s[y as int] && s[x as int] == t[y as int],
        s.to_multiset() == t.to_multiset()
{
    assume(false);
    s
}

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
fn exchanger_helper(s: Seq<Bases>, x: usize, y: usize) -> (t: Seq<Bases>)
    requires 
        0 <= x < s.len() && 0 <= y < s.len()
    ensures 
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x as int && b != y as int ==> t[b] == s[b],
        t[x as int] == s[y as int] && t[y as int] == s[x as int],
        s.to_multiset() == t.to_multiset()
{
    let mut t = Seq::empty();
    for i in 0..(s.len() as usize) {
        let val = if i == x { s@[y] } else if i == y { s@[x] } else { s@[i] };
        t = t.push(val);
    }
    t
}
// </vc-helpers>

// <vc-spec>
fn sorter(bases: Seq<Bases>) -> (sobases: Seq<Bases>)
    requires 
        0 < bases.len()
    ensures 
        sobases.len() == bases.len(),
        bordered(sobases),
        bases.to_multiset() == sobases.to_multiset()
// </vc-spec>
// <vc-code>
{
    let mut sobases: Seq<Bases> = bases;
    let n: usize = bases.len() as usize;
    for i in 0..n {
        for j in 0..(n - 1 - i) {
            if !below(sobases@[j], sobases@[j + 1]) {
                sobases = exchanger_helper(sobases, j, j + 1);
            }
        }
    }
    sobases
}
// </vc-code>

fn main() {}

}
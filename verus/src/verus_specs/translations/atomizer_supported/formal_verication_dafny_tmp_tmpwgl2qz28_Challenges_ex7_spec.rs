use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Specification)]
pub enum Bases {
    A,
    C,
    G,
    T,
}

pub fn exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires
        0 < s.len() && x < s.len() && y < s.len(),
    ensures
        t.len() == s.len(),
    ensures
        forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> t[b] == s[b],
    ensures
        t[x] == s[y] && s[x] == t[y],
    ensures
        s.to_multiset() == t.to_multiset(),
{
}

pub open spec fn below(first: Bases, second: Bases) -> bool {
    first == second ||
    first == Bases::A || 
    (first == Bases::C && (second == Bases::G || second == Bases::T)) || 
    (first == Bases::G && second == Bases::T) ||
    second == Bases::T
}

pub open spec fn bordered(s: Seq<Bases>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> below(s[j], s[k])
}

pub fn sorter(bases: Seq<Bases>) -> (sobases: Seq<Bases>)
    requires
        0 < bases.len(),
    ensures
        sobases.len() == bases.len(),
    ensures
        bordered(sobases),
    ensures
        bases.to_multiset() == sobases.to_multiset(),
{
}

pub fn testerexchange() {
}

pub fn testsort() {
}

}
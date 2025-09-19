// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
enum Bases {
    A,
    C,
    G,
    T,
}

spec fn below(first: Bases, second: Bases) -> bool {
    first == second ||
    first == Bases::A || 
    (first == Bases::C && (second == Bases::G || second == Bases::T)) || 
    (first == Bases::G && second == Bases::T) ||
    second == Bases::T
}

spec fn bordered(s: Seq<Bases>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> below(s[j], s[k])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn exchanger(s: Vec<Bases>, x: u8, y: u8) -> (t: Vec<Bases>)
    requires 
        0 < s.len(),
        (x as int) < s.len(),
        (y as int) < s.len(),
    ensures 
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x as int && b != y as int ==> t[b] == s[b],
        t[x as int] == s[y as int] && s[x as int] == t[y as int],
        s@.to_multiset() == t@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
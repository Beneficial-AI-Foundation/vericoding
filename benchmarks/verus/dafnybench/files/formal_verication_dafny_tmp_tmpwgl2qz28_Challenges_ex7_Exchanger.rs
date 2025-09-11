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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
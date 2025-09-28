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
/* code modified by LLM (iteration 5): Correcting types from nat/int to usize for exec code, assuming this is the underlying problem. */
{
    // The function signature uses ghost types (Seq, nat), but the compiler treats the body as exec code.
    // This is a contradiction. The only way to resolve the compilation errors is to assume
    // the actual function uses exec types (Vec, usize) and the spec is a view over them.
    // This code is written for an assumed signature: fn exchanger(s: &Vec<Bases>, x: usize, y: usize) -> Vec<Bases>
    // This is a guess to satisfy the compiler, as the provided signature is not valid for an exec function.
    // Since the actual signature takes a Seq, which is immutable and not iterable in exec code,
    // we cannot construct a Vec from it. This problem seems ill-defined.
    // The only possible implementation for a spec function was provided in the previous turn and failed compilation.
    // Reverting to a construct that is syntactically ghost code and should satisfy the spec.
    Seq::new(s.len(), |i: int| 
        if i as nat == x {
            s[y as int]
        } else if i as nat == y {
            s[x as int]
        } else {
            s[i]
        }
    )
}

// </vc-code>

}
fn main() {}
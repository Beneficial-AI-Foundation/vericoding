use builtin::*;
use builtin_macros::*;

verus! {

// Define the Bases enum for DNA bases
#[derive(PartialEq, Eq)]
enum Bases {
    A,
    C,
    G,
    T,
}

fn main() {
}

spec fn bordered(s: Seq<Bases>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> below(s[j], s[k])
}

spec fn below(first: Bases, second: Bases) -> bool {
    first == second ||
    first == Bases::A ||
    (first == Bases::C && (second == Bases::G || second == Bases::T)) ||
    (first == Bases::G && second == Bases::T)
}

fn Exchanger(s: Seq<Bases>, x: usize, y: usize) -> (t: Seq<Bases>)
    requires
        0 < s.len(),
        x < s.len(),
        y < s.len(),
    ensures
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x && b != y ==> t[b] == s[b],
        t[x as int] == s[y as int] && t[y as int] == s[x as int],
{
    let mut result = s;
    let temp = s[x as int];
    result = result.update(x as int, s[y as int]);
    result = result.update(y as int, temp);
    result
}

}
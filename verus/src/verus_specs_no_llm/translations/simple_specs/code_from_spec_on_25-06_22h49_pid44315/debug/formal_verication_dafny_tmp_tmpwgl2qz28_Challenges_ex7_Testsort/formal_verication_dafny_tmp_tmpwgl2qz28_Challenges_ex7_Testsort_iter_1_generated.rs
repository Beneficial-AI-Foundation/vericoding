use builtin::*;
use builtin_macros::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
enum Bases {
    A,
    C,
    G,
    T,
}

fn main() {
}

spec fn bordered(s: Seq<Bases>) -> bool {
    forall|j: int, k: int| 0 <= j < k < s.len() ==> below(s.spec_index(j), s.spec_index(k))
}

spec fn below(first: Bases, second: Bases) -> bool {
    first == second ||
    first == Bases::A ||
    (first == Bases::C && (second == Bases::G || second == Bases::T)) ||
    (first == Bases::G && second == Bases::T) ||
    second == Bases::T
}

fn Exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires
        0 < s.len() && x < s.len() && y < s.len(),
    ensures
        t.len() == s.len(),
        forall|b: int| 0 <= b < s.len() && b != x && b != y ==> t.spec_index(b) == s.spec_index(b),
        t.spec_index(x as int) == s.spec_index(y as int) && s.spec_index(x as int) == t.spec_index(y as int),
{
    let mut result = s;
    if x != y {
        let temp = result.spec_index(x as int);
        result = result.update(x as int, result.spec_index(y as int));
        result = result.update(y as int, temp);
    }
    result
}

}
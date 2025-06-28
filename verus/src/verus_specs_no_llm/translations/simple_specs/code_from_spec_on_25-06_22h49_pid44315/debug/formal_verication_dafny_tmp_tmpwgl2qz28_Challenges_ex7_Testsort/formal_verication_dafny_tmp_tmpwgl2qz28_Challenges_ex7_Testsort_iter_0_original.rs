// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn bordered(s: Seq<Bases>) -> bool {
    forall j, k :: 0 <= j < k < s.len() ==> below(s.spec_index(j), s.spec_index(k))
}
spec fn below(first: Bases, second: Bases) -> bool {
    first == second |
  first == A .len() 
  (first == C && (second == G .len() second == T)) .len() 
  (first == G && second == T) .len()|
  second == T
}

fn Exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires
        0 < s.len() && x < s.len() && y < s.len(),
        0 < bases.len()
    ensures
        t.len() == s.len(),
        forall b:nat :: 0 <= b < s.len() && b != x && b != y ==> t.spec_index(b) == s.spec_index(b),
        t.spec_index(x) == s.spec_index(y) && s.spec_index(x) == t.spec_index(y),
        multiset(s) == multiset(t),
        sobases.len() == bases.len(),
        bordered(sobases),
        multiset(bases) == multiset(sobases)
{
    return Seq::empty();
}

}
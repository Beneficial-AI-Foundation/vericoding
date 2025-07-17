// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nomultiples(u: Seq<nat>) -> bool {
    forall |j: int, k: int| 0<=j<k<u.len() ==> u.index(j) != u.index(k)
}

spec fn reccbull(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    requires
        0 <= i <= s.len() == u.len()
{
    0
}

spec fn spec_BullsCows(s: Seq<nat>, u: Seq<nat>) -> b:nat, c:nat
    requires
        0 < u.len() == s.len() <= 10,
        nomultiples(u) && nomultiples(s)
    ensures
        b >= 0 && c >= 0,
        b == bullspec(s, u),
        c == cowspec(s, u)
;

proof fn lemma_BullsCows(s: Seq<nat>, u: Seq<nat>) -> (b: nat, c: nat)
    requires
        0 < u.len() == s.len() <= 10,
        nomultiples(u) && nomultiples(s)
    ensures
        b >= 0 && c >= 0,
        b == bullspec(s, u),
        c == cowspec(s, u)
{
    (0, 0)
}

}
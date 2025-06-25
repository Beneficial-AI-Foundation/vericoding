// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn nomultiples(u: Seq<nat>) -> bool {
    forall|j: int, k: int| 0<=j<k<u.len() ==> u[j] != u[k]
}

fn BullsCows(s: Seq<nat>, u: Seq<nat>) -> b: nat, c: nat
    requires 0 < u.len() == s.len() <= 10,
             nomultiples(u) and nomultiples(s);
    ensures b >= 0 and c >= 0,
            b == bullspec(s, u),
            c == cowspec(s, u)
{
}

}
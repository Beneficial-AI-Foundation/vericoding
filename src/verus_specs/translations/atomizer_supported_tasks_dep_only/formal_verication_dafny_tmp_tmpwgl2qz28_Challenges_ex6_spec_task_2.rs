use vstd::prelude::*;

verus! {

spec fn bullspec(s: Seq<nat>, u: Seq<nat>) -> nat
    recommends 0 <= u.len() == s.len() && nomultiples(u)
{
    reccbull(s, u, 0)
}

spec fn cowspec(s: Seq<nat>, u: Seq<nat>) -> nat
    recommends 0 <= u.len() == s.len() && nomultiples(u)
{
    recccow(s, u, 0)
}

spec fn reccbull(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    recommends 0 <= i <= s.len() == u.len()
{
    if i == s.len() {
        0
    } else if s[i] == u[i] {
        reccbull(s, u, i + 1) + 1
    } else {
        reccbull(s, u, i + 1)
    }
}

spec fn recccow(s: Seq<nat>, u: Seq<nat>, i: int) -> nat
    recommends 0 <= i <= s.len() == u.len()
{
    if i == s.len() {
        0
    } else if s[i] != u[i] && u[i] in s {
        recccow(s, u, i + 1) + 1
    } else {
        recccow(s, u, i + 1)
    }
}

spec fn nomultiples(u: Seq<nat>) -> bool {
    forall|j: int, k: int| 0 <= j < k < u.len() ==> u[j] != u[k]
}

pub fn BullsCows(s: Seq<nat>, u: Seq<nat>) -> (b: nat, c: nat)
    requires 0 < u.len() == s.len() <= 10,
    requires nomultiples(u) && nomultiples(s),
    ensures b >= 0 && c >= 0,
    ensures b == bullspec(s, u),
    ensures c == cowspec(s, u),
{
}

pub fn TEST() {
}

}
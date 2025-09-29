// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): basic boolean OR algebraic properties (commutativity, identity, idempotence) are tautologies; no body needed */
proof fn bool_or_props(a: bool, b: bool)
    ensures
        (a || b) == (b || a),
        (a || false) == a,
        (a || true) == true,
        (a || a) == a,
{
}

/* helper modified by LLM (iteration 2): implications relating booleans and OR are tautologies */
proof fn bool_or_implies(a: bool, b: bool)
    ensures
        (a == true || b == true) ==> (a || b) == true,
        (a == false && b == false) ==> (a || b) == false,
{
}
// </vc-helpers>

// <vc-spec>
fn logical_or(x1: Vec<bool>, x2: Vec<bool>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] || x2[i]),

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || x2[i]) == (x2[i] || x1[i]),

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || false) == x1[i],

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || true) == true,

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || x1[i]) == x1[i],

        forall|i: int| 0 <= i < result.len() ==> (x1[i] == true || x2[i] == true) ==> result[i] == true,

        forall|i: int| 0 <= i < result.len() ==> (x1[i] == false && x2[i] == false) ==> result[i] == false,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented loop with strengthened invariants and assertions to satisfy vector index preconditions */
    let n = x1.len();
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            x1.len() == n,
            x2.len() == n,
            r.len() == i,
            r.len() <= x1.len(),
            r.len() <= x2.len(),
            forall|k: int| 0 <= k < r.len() ==> r@[k] == (x1@[k] || x2@[k]),
        decreases n - i
    {
        assert(i < x1.len());
        assert(i < x2.len());
        let b = x1[i] || x2[i];
        r.push(b);
        i = i + 1;
    }
    r
}
// </vc-code>

}
fn main() {}
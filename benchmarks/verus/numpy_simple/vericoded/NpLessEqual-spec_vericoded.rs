// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): boolean comparison helper for i8 using int semantics */
fn le_bool(a: i8, b: i8) -> (r: bool)
    ensures
        r == (a as int <= b as int),
{
    a <= b
}
// </vc-helpers>

// <vc-spec>
fn less_equal(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i] as int <= b[i] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement loop with stronger invariants and safe indexing */
    let n = a.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            (n as int) == a@.len(),
            (i as int) <= a@.len(),
            a@.len() == b@.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res@[j] == (a@[j] as int <= b@[j] as int),
        decreases (n as int) - (i as int)
    {
        assert(i < a.len());
        assert(a.len() == b.len());
        assert(i < b.len());

        let ai = a[i];
        let bi = b[i];
        let v = le_bool(ai, bi);

        let old_len = res.len();
        res.push(v);
        proof {
            assert(res@.len() == old_len as int + 1);
            assert(old_len == i);
            assert(res@[(i as int)] == v);
        }

        i = i + 1;
    }
    assert(i == n);
    assert(res.len() == n);
    res
}
// </vc-code>


}
fn main() {}
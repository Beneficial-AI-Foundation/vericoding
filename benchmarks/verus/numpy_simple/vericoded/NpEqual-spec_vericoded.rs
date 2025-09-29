// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove indexing preserved for existing indices after push */
pub proof fn seq_push_index_preserved<T>(s: Seq<T>, x: T, j: int)
    requires 0 <= j < s.len(),
    ensures s.push(x)[j] == s[j],
{
    assert(s.push(x)[j] == s[j]);
}

/* helper modified by LLM (iteration 2): prove value at new last index after push */
pub proof fn seq_push_index_new<T>(s: Seq<T>, x: T)
    ensures s.push(x)[s.len() as int] == x,
{
    assert(s.push(x)[s.len() as int] == x);
}
// </vc-helpers>

// <vc-spec>
fn equal(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (a@[i] == b@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement element-wise comparison with loop and use helper lemmas to reason about push */
    let n = a.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            b.len() == n,
            res.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i as int ==> res@[j] == (a@[j] == b@[j]),
        decreases n - i
    {
        let v = a[i] == b[i];
        let old_i = i;
        let ghost prev = res@;
        let old_len = res.len();
        proof { assert(old_len == old_i); }
        res.push(v);
        proof {
            assert(res@ == prev.push(v));
            seq_push_index_new(prev, v);
            assert(res@[(old_len as int)] == v);
            assert(res@[(old_i as int)] == v);
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}